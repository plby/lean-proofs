/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate514 : CompactCertificate where
  left := 385
  right := 386
  center := 771 / 2
  grid := fun i =>
    match i.val with
    | 0 => 123
    | 1 => 90
    | 2 => 146
    | 3 => 26
    | 4 => 71
    | 5 => 192
    | 6 => 142
    | 7 => 243
    | 8 => 179
    | 9 => 275
    | 10 => 158
    | 11 => 281
    | 12 => 263
    | 13 => 188
    | 14 => 213
    | 15 => 177
    | 16 => 157
    | 17 => 227
    | 18 => 126
    | 19 => 106
    | 20 => 67
    | 21 => 36
    | 22 => 97
    | 23 => 133
    | 24 => 56
    | 25 => 228
    | _ => 152
  point := fun i =>
    match i.val with
    | 0 => 771 / 2
    | 1 => 1135830220831671 / 4000000000000
    | 2 => 367304156312343 / 800000000000
    | 3 => 331432425637797 / 4000000000000
    | 4 => 890274115090209 / 4000000000000
    | 5 => 2417267405449053 / 4000000000000
    | 6 => 1780548230181189 / 4000000000000
    | 7 => 3050999740887897 / 4000000000000
    | 8 => 2247352600160523 / 4000000000000
    | 9 => 3448016821304229 / 4000000000000
    | 10 => 1990713439950141 / 4000000000000
    | 11 => 3532555932875169 / 4000000000000
    | 12 => 3300571983595461 / 4000000000000
    | 13 => 2355443907206613 / 4000000000000
    | 14 => 2670822345270627 / 4000000000000
    | 15 => 2226653224259763 / 4000000000000
    | 16 => 1967315651251023 / 4000000000000
    | 17 => 570204755543277 / 800000000000
    | 18 => 1577216362064919 / 4000000000000
    | 19 => 1337023777315359 / 4000000000000
    | 20 => 836647399839477 / 4000000000000
    | 21 => 449951754197259 / 4000000000000
    | 22 => 1221706540728777 / 4000000000000
    | 23 => 1668135834460329 / 4000000000000
    | 24 => 705352600160523 / 4000000000000
    | 25 => 2867219159647083 / 4000000000000
    | _ => 1915169520056997 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))
    | 1 => (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))
    | 2 => (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000))
    | 3 => (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))
    | 4 => (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
    | 5 => (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000))
    | 6 => (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))
    | 7 => (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))
    | 8 => (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000))
    | 9 => (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))
    | 10 => (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))
    | 11 => (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000))
    | 12 => (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))
    | 13 => (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))
    | 14 => (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000))
    | 15 => (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))
    | 16 => (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))
    | 17 => (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000))
    | 18 => (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))
    | 19 => (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))
    | 20 => (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000))
    | 21 => (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))
    | 22 => (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))
    | 23 => (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000))
    | 24 => (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))
    | 25 => (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))
    | _ => (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4571132494 / 1000000000000) (4571132683 / 1000000000000)
      | 1 => orderedInterval (-3628283938 / 1000000000000) (-3628281306 / 1000000000000)
      | 2 => orderedInterval (-109564299 / 1000000000000) (-109564276 / 1000000000000)
      | 3 => orderedInterval (-5569157150 / 1000000000000) (-5569138678 / 1000000000000)
      | 4 => orderedInterval (-2820592888 / 1000000000000) (-2820588711 / 1000000000000)
      | 5 => orderedInterval (-1871187903 / 1000000000000) (-1871187750 / 1000000000000)
      | 6 => orderedInterval (3098014159 / 1000000000000) (3098018281 / 1000000000000)
      | 7 => orderedInterval (751294576 / 1000000000000) (751294623 / 1000000000000)
      | _ => orderedInterval (-8058952683 / 1000000000000) (-8058939520 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15272226038 / 1000000000000) (-15272225888 / 1000000000000)
      | 1 => orderedInterval (230247846 / 1000000000000) (230251891 / 1000000000000)
      | 2 => orderedInterval (608719982 / 1000000000000) (608720020 / 1000000000000)
      | 3 => orderedInterval (-948048587 / 1000000000000) (-948014498 / 1000000000000)
      | 4 => orderedInterval (3910105893 / 1000000000000) (3910112279 / 1000000000000)
      | 5 => orderedInterval (739791782 / 1000000000000) (739791983 / 1000000000000)
      | 6 => orderedInterval (-4687899695 / 1000000000000) (-4687895815 / 1000000000000)
      | 7 => orderedInterval (2915644633 / 1000000000000) (2915644676 / 1000000000000)
      | _ => orderedInterval (2853617526 / 1000000000000) (2853633896 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5213601361 / 1000000000000) (-5213601237 / 1000000000000)
      | 1 => orderedInterval (5567734595 / 1000000000000) (5567740924 / 1000000000000)
      | 2 => orderedInterval (27205861 / 1000000000000) (27205929 / 1000000000000)
      | 3 => orderedInterval (36368418092 / 1000000000000) (36368485096 / 1000000000000)
      | 4 => orderedInterval (6980372826 / 1000000000000) (6980382609 / 1000000000000)
      | 5 => orderedInterval (3752615110 / 1000000000000) (3752615378 / 1000000000000)
      | 6 => orderedInterval (-3185817474 / 1000000000000) (-3185813762 / 1000000000000)
      | 7 => orderedInterval (-589567977 / 1000000000000) (-589567934 / 1000000000000)
      | _ => orderedInterval (17357529700 / 1000000000000) (17357550114 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14873932914 / 1000000000000) (14873933021 / 1000000000000)
      | 1 => orderedInterval (-2676199055 / 1000000000000) (-2676189142 / 1000000000000)
      | 2 => orderedInterval (-4424182692 / 1000000000000) (-4424182570 / 1000000000000)
      | 3 => orderedInterval (-129384698 / 1000000000000) (-129246910 / 1000000000000)
      | 4 => orderedInterval (-11581366658 / 1000000000000) (-11581351690 / 1000000000000)
      | 5 => orderedInterval (1166347861 / 1000000000000) (1166348224 / 1000000000000)
      | 6 => orderedInterval (4564950225 / 1000000000000) (4564953801 / 1000000000000)
      | 7 => orderedInterval (-3802496824 / 1000000000000) (-3802496781 / 1000000000000)
      | _ => orderedInterval (-2118865618 / 1000000000000) (-2118840185 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (6304340695 / 1000000000000) (6304340792 / 1000000000000)
      | 1 => orderedInterval (-13162915508 / 1000000000000) (-13162899947 / 1000000000000)
      | 2 => orderedInterval (760206037 / 1000000000000) (760206263 / 1000000000000)
      | 3 => orderedInterval (-199107594718 / 1000000000000) (-199107301779 / 1000000000000)
      | 4 => orderedInterval (-18023480920 / 1000000000000) (-18023457968 / 1000000000000)
      | 5 => orderedInterval (-8306110139 / 1000000000000) (-8306109636 / 1000000000000)
      | 6 => orderedInterval (3607152505 / 1000000000000) (3607155988 / 1000000000000)
      | 7 => orderedInterval (371953631 / 1000000000000) (371953676 / 1000000000000)
      | _ => orderedInterval (-42374111299 / 1000000000000) (-42374079502 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13637297632 / 1000000000000) (-13637254654 / 1000000000000)
    | 1 => orderedInterval (-9650046658 / 1000000000000) (-9649981456 / 1000000000000)
    | 2 => orderedInterval (61064889372 / 1000000000000) (61064997117 / 1000000000000)
    | 3 => orderedInterval (-4127264545 / 1000000000000) (-4127072232 / 1000000000000)
    | _ => orderedInterval (-269930559716 / 1000000000000) (-269930192113 / 1000000000000)

theorem compactCertificate514_stateChecks0 :
    compactCertificate514.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (771 / 2)) (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1135830220831671 / 4000000000000)) (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (367304156312343 / 800000000000)) (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks1 :
    compactCertificate514.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (331432425637797 / 4000000000000)) (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (890274115090209 / 4000000000000)) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2417267405449053 / 4000000000000)) (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks2 :
    compactCertificate514.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1780548230181189 / 4000000000000)) (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3050999740887897 / 4000000000000)) (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2247352600160523 / 4000000000000)) (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks3 :
    compactCertificate514.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3448016821304229 / 4000000000000)) (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1990713439950141 / 4000000000000)) (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3532555932875169 / 4000000000000)) (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks4 :
    compactCertificate514.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3300571983595461 / 4000000000000)) (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2355443907206613 / 4000000000000)) (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2670822345270627 / 4000000000000)) (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks5 :
    compactCertificate514.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2226653224259763 / 4000000000000)) (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1967315651251023 / 4000000000000)) (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (570204755543277 / 800000000000)) (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks6 :
    compactCertificate514.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1577216362064919 / 4000000000000)) (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1337023777315359 / 4000000000000)) (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (836647399839477 / 4000000000000)) (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks7 :
    compactCertificate514.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (449951754197259 / 4000000000000)) (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221706540728777 / 4000000000000)) (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1668135834460329 / 4000000000000)) (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_stateChecks8 :
    compactCertificate514.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (705352600160523 / 4000000000000)) (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2867219159647083 / 4000000000000)) (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1915169520056997 / 4000000000000)) (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_states : ∀ j,
    BesselStateValid (compactCertificate514.point j) (compactCertificate514.state j) :=
  compactCertificate514.statesValid_of_checks3 compactCertificate514_stateChecks0
    compactCertificate514_stateChecks1 compactCertificate514_stateChecks2
    compactCertificate514_stateChecks3 compactCertificate514_stateChecks4
    compactCertificate514_stateChecks5 compactCertificate514_stateChecks6
    compactCertificate514_stateChecks7 compactCertificate514_stateChecks8

theorem compactCertificate514_chunkChecks0_0 :
    compactCertificate514.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (771 / 2) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1135830220831671 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (367304156312343 / 800000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000)))) (orderedInterval (4571132494 / 1000000000000) (4571132683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (331432425637797 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2417267405449053 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000)))) (orderedInterval (-3628283938 / 1000000000000) (-3628281306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1780548230181189 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3050999740887897 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2247352600160523 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000)))) (orderedInterval (-109564299 / 1000000000000) (-109564276 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks0_1 :
    compactCertificate514.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3448016821304229 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1990713439950141 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3532555932875169 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000)))) (orderedInterval (-5569157150 / 1000000000000) (-5569138678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3300571983595461 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2355443907206613 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2670822345270627 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000)))) (orderedInterval (-2820592888 / 1000000000000) (-2820588711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2226653224259763 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1967315651251023 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (570204755543277 / 800000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000)))) (orderedInterval (-1871187903 / 1000000000000) (-1871187750 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks0_2 :
    compactCertificate514.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1577216362064919 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1337023777315359 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (836647399839477 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000)))) (orderedInterval (3098014159 / 1000000000000) (3098018281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (449951754197259 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1221706540728777 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1668135834460329 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000)))) (orderedInterval (751294576 / 1000000000000) (751294623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (705352600160523 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2867219159647083 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1915169520056997 / 4000000000000) 0 (IntervalRat.scale (771 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000)))) (orderedInterval (-8058952683 / 1000000000000) (-8058939520 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks0 :
    compactCertificate514.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate514.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate514_chunkChecks0_0
    compactCertificate514_chunkChecks0_1 compactCertificate514_chunkChecks0_2

theorem compactCertificate514_chunkChecks1_0 :
    compactCertificate514.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (771 / 2) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1135830220831671 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (367304156312343 / 800000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000)))) (orderedInterval (-15272226038 / 1000000000000) (-15272225888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (331432425637797 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2417267405449053 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000)))) (orderedInterval (230247846 / 1000000000000) (230251891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1780548230181189 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3050999740887897 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2247352600160523 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000)))) (orderedInterval (608719982 / 1000000000000) (608720020 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks1_1 :
    compactCertificate514.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3448016821304229 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1990713439950141 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3532555932875169 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000)))) (orderedInterval (-948048587 / 1000000000000) (-948014498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3300571983595461 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2355443907206613 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2670822345270627 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000)))) (orderedInterval (3910105893 / 1000000000000) (3910112279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2226653224259763 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1967315651251023 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (570204755543277 / 800000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000)))) (orderedInterval (739791782 / 1000000000000) (739791983 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks1_2 :
    compactCertificate514.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1577216362064919 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1337023777315359 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (836647399839477 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000)))) (orderedInterval (-4687899695 / 1000000000000) (-4687895815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (449951754197259 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1221706540728777 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1668135834460329 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000)))) (orderedInterval (2915644633 / 1000000000000) (2915644676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (705352600160523 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2867219159647083 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1915169520056997 / 4000000000000) 1 (IntervalRat.scale (771 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000)))) (orderedInterval (2853617526 / 1000000000000) (2853633896 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks1 :
    compactCertificate514.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate514.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate514_chunkChecks1_0
    compactCertificate514_chunkChecks1_1 compactCertificate514_chunkChecks1_2

theorem compactCertificate514_chunkChecks2_0 :
    compactCertificate514.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (771 / 2) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1135830220831671 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (367304156312343 / 800000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000)))) (orderedInterval (-5213601361 / 1000000000000) (-5213601237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (331432425637797 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2417267405449053 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000)))) (orderedInterval (5567734595 / 1000000000000) (5567740924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1780548230181189 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3050999740887897 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2247352600160523 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000)))) (orderedInterval (27205861 / 1000000000000) (27205929 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks2_1 :
    compactCertificate514.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3448016821304229 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1990713439950141 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3532555932875169 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000)))) (orderedInterval (36368418092 / 1000000000000) (36368485096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3300571983595461 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2355443907206613 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2670822345270627 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000)))) (orderedInterval (6980372826 / 1000000000000) (6980382609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2226653224259763 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1967315651251023 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (570204755543277 / 800000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000)))) (orderedInterval (3752615110 / 1000000000000) (3752615378 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks2_2 :
    compactCertificate514.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1577216362064919 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1337023777315359 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (836647399839477 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000)))) (orderedInterval (-3185817474 / 1000000000000) (-3185813762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (449951754197259 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1221706540728777 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1668135834460329 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000)))) (orderedInterval (-589567977 / 1000000000000) (-589567934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (705352600160523 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2867219159647083 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1915169520056997 / 4000000000000) 2 (IntervalRat.scale (771 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000)))) (orderedInterval (17357529700 / 1000000000000) (17357550114 / 1000000000000))) = true
  rfl'

theorem compactCertificate514_chunkChecks2 :
    compactCertificate514.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate514.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate514_chunkChecks2_0
    compactCertificate514_chunkChecks2_1 compactCertificate514_chunkChecks2_2

theorem compactCertificate514_chunkChecks3_0 :
    compactCertificate514.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (771 / 2) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1135830220831671 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (367304156312343 / 800000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000)))) (orderedInterval (14873932914 / 1000000000000) (14873933021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (331432425637797 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2417267405449053 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000)))) (orderedInterval (-2676199055 / 1000000000000) (-2676189142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1780548230181189 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3050999740887897 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2247352600160523 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000)))) (orderedInterval (-4424182692 / 1000000000000) (-4424182570 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate514_chunkChecks3_1 :
    compactCertificate514.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3448016821304229 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1990713439950141 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3532555932875169 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000)))) (orderedInterval (-129384698 / 1000000000000) (-129246910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3300571983595461 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2355443907206613 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2670822345270627 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000)))) (orderedInterval (-11581366658 / 1000000000000) (-11581351690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2226653224259763 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1967315651251023 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (570204755543277 / 800000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000)))) (orderedInterval (1166347861 / 1000000000000) (1166348224 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate514_chunkChecks3_2 :
    compactCertificate514.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1577216362064919 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1337023777315359 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (836647399839477 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000)))) (orderedInterval (4564950225 / 1000000000000) (4564953801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (449951754197259 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1221706540728777 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1668135834460329 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000)))) (orderedInterval (-3802496824 / 1000000000000) (-3802496781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (705352600160523 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2867219159647083 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1915169520056997 / 4000000000000) 3 (IntervalRat.scale (771 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000)))) (orderedInterval (-2118865618 / 1000000000000) (-2118840185 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate514_chunkChecks3 :
    compactCertificate514.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate514.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate514_chunkChecks3_0
    compactCertificate514_chunkChecks3_1 compactCertificate514_chunkChecks3_2

theorem compactCertificate514_chunkChecks4_0 :
    compactCertificate514.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (771 / 2) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5301155839 / 1000000000000) (5301155844 / 1000000000000), orderedInterval (-40297224976 / 1000000000000) (-40297224970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1135830220831671 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43070787308 / 1000000000000) (43070804393 / 1000000000000), orderedInterval (-19744560140 / 1000000000000) (-19744543055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (367304156312343 / 800000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35251594130 / 1000000000000) (35251594133 / 1000000000000), orderedInterval (11957540577 / 1000000000000) (11957540580 / 1000000000000)))) (orderedInterval (6304340695 / 1000000000000) (6304340792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (331432425637797 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81078362722 / 1000000000000) (81078366898 / 1000000000000), orderedInterval (-33797681916 / 1000000000000) (-33797677740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2417267405449053 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30539397408 / 1000000000000) (30539433144 / 1000000000000), orderedInterval (-11016073370 / 1000000000000) (-11016037633 / 1000000000000)))) (orderedInterval (-13162915508 / 1000000000000) (-13162899947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1780548230181189 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6918553622 / 1000000000000) (-6918553614 / 1000000000000), orderedInterval (37187069312 / 1000000000000) (37187069320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3050999740887897 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3692274417 / 1000000000000) (-3692274416 / 1000000000000), orderedInterval (-28650762338 / 1000000000000) (-28650762337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2247352600160523 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9245636946 / 1000000000000) (-9245636945 / 1000000000000), orderedInterval (-32358735004 / 1000000000000) (-32358735003 / 1000000000000)))) (orderedInterval (760206037 / 1000000000000) (760206263 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate514_chunkChecks4_1 :
    compactCertificate514.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3448016821304229 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24788787729 / 1000000000000) (24788847998 / 1000000000000), orderedInterval (-11152128367 / 1000000000000) (-11152068098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1990713439950141 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31018967291 / 1000000000000) (31019069959 / 1000000000000), orderedInterval (-17835685248 / 1000000000000) (-17835582580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3532555932875169 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24358668902 / 1000000000000) (-24358668883 / 1000000000000), orderedInterval (-11278481064 / 1000000000000) (-11278481046 / 1000000000000)))) (orderedInterval (-199107594718 / 1000000000000) (-199107301779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3300571983595461 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8489959629 / 1000000000000) (8489959632 / 1000000000000), orderedInterval (-26452210601 / 1000000000000) (-26452210598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2355443907206613 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27182754192 / 1000000000000) (-27182710583 / 1000000000000), orderedInterval (18521776657 / 1000000000000) (18521820265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2670822345270627 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19136901534 / 1000000000000) (19136902849 / 1000000000000), orderedInterval (-24247012782 / 1000000000000) (-24247011468 / 1000000000000)))) (orderedInterval (-18023480920 / 1000000000000) (-18023457968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2226653224259763 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33245478070 / 1000000000000) (-33245478005 / 1000000000000), orderedInterval (-6164732872 / 1000000000000) (-6164732807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1967315651251023 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20786692313 / 1000000000000) (20786694315 / 1000000000000), orderedInterval (-29386186015 / 1000000000000) (-29386184013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (570204755543277 / 800000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11628152420 / 1000000000000) (-11628152419 / 1000000000000), orderedInterval (-27523039876 / 1000000000000) (-27523039875 / 1000000000000)))) (orderedInterval (-8306110139 / 1000000000000) (-8306109636 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate514_chunkChecks4_2 :
    compactCertificate514.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1577216362064919 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27433303096 / 1000000000000) (-27433289232 / 1000000000000), orderedInterval (29393840691 / 1000000000000) (29393854555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1337023777315359 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39078902785 / 1000000000000) (39078932322 / 1000000000000), orderedInterval (-19485889956 / 1000000000000) (-19485860419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (836647399839477 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28367278846 / 1000000000000) (28367283024 / 1000000000000), orderedInterval (-47385590852 / 1000000000000) (-47385586674 / 1000000000000)))) (orderedInterval (3607152505 / 1000000000000) (3607155988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (449951754197259 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13089821540 / 1000000000000) (13089821541 / 1000000000000), orderedInterval (74023922884 / 1000000000000) (74023922885 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1221706540728777 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45454688086 / 1000000000000) (-45454688049 / 1000000000000), orderedInterval (-4195356173 / 1000000000000) (-4195356135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1668135834460329 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (498761919 / 1000000000000) (498761920 / 1000000000000), orderedInterval (-39068412610 / 1000000000000) (-39068412608 / 1000000000000)))) (orderedInterval (371953631 / 1000000000000) (371953676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (705352600160523 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55862200846 / 1000000000000) (55862200847 / 1000000000000), orderedInterval (21969086691 / 1000000000000) (21969086692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2867219159647083 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28769808120 / 1000000000000) (28769808186 / 1000000000000), orderedInterval (7753826713 / 1000000000000) (7753826779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1915169520056997 / 4000000000000) 4 (IntervalRat.scale (771 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32265063127 / 1000000000000) (32265132685 / 1000000000000), orderedInterval (-17021941007 / 1000000000000) (-17021871449 / 1000000000000)))) (orderedInterval (-42374111299 / 1000000000000) (-42374079502 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate514_chunkChecks4 :
    compactCertificate514.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate514.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate514_chunkChecks4_0
    compactCertificate514_chunkChecks4_1 compactCertificate514_chunkChecks4_2

theorem compactCertificate514_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate514.chunkCheck r b = true :=
  compactCertificate514.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate514_chunkChecks0
    · exact compactCertificate514_chunkChecks1
    · exact compactCertificate514_chunkChecks2
    · exact compactCertificate514_chunkChecks3
    · exact compactCertificate514_chunkChecks4)

theorem compactCertificate514_coefficient0 :
    compactCertificate514.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate514_coefficient1 :
    compactCertificate514.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate514_coefficient2 :
    compactCertificate514.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate514_coefficient3 :
    compactCertificate514.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate514_coefficient4 :
    compactCertificate514.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate514_coefficients : ∀ r : Fin 5,
    compactCertificate514.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate514_coefficient0
  · exact compactCertificate514_coefficient1
  · exact compactCertificate514_coefficient2
  · exact compactCertificate514_coefficient3
  · exact compactCertificate514_coefficient4

theorem compactCertificate514_lower : (1 : ℚ) ≤ compactCertificate514.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate514, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate514_proves {t : ℝ} (ht : t ∈ compactCertificate514.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate514.proves compactCertificate514_states compactCertificate514_chunks
    compactCertificate514_coefficients compactCertificate514_lower ht

end Erdos232
