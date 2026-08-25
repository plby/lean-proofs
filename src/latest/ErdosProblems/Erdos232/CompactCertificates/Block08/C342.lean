/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate342 : CompactCertificate where
  left := 214
  right := 215
  center := 429 / 2
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
    | 8 => 100
    | 9 => 153
    | 10 => 88
    | 11 => 156
    | 12 => 146
    | 13 => 104
    | 14 => 118
    | 15 => 99
    | 16 => 87
    | 17 => 126
    | 18 => 70
    | 19 => 59
    | 20 => 37
    | 21 => 20
    | 22 => 54
    | 23 => 74
    | 24 => 31
    | 25 => 127
    | _ => 85
  point := fun i =>
    match i.val with
    | 0 => 429 / 2
    | 1 => 631998916649529 / 4000000000000
    | 2 => 204375464407257 / 800000000000
    | 3 => 184415707650603 / 4000000000000
    | 4 => 495366530964591 / 4000000000000
    | 5 => 1345016494082547 / 4000000000000
    | 6 => 990733061929611 / 4000000000000
    | 7 => 1697637988120503 / 4000000000000
    | 8 => 1250472458455077 / 4000000000000
    | 9 => 1918546324694571 / 4000000000000
    | 10 => 1107673237015059 / 4000000000000
    | 11 => 1965585596891631 / 4000000000000
    | 12 => 1836505033673739 / 4000000000000
    | 13 => 1310616648756987 / 4000000000000
    | 14 => 1486099592893773 / 4000000000000
    | 15 => 1238954906883837 / 4000000000000
    | 16 => 1094654233964577 / 4000000000000
    | 17 => 317273463201123 / 800000000000
    | 18 => 877595096401881 / 4000000000000
    | 19 => 743947082319441 / 4000000000000
    | 20 => 465527541544923 / 4000000000000
    | 21 => 250362260117541 / 4000000000000
    | 22 => 679782238615623 / 4000000000000
    | 23 => 928184530458471 / 4000000000000
    | 24 => 392472458455077 / 4000000000000
    | 25 => 1595378754200517 / 4000000000000
    | _ => 1065639071471403 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))
    | 1 => (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))
    | 2 => (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000))
    | 3 => (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))
    | 4 => (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))
    | 5 => (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000))
    | 6 => (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))
    | 7 => (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))
    | 8 => (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000))
    | 9 => (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))
    | 10 => (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))
    | 11 => (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000))
    | 12 => (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))
    | 13 => (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))
    | 14 => (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000))
    | 15 => (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))
    | 16 => (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))
    | 17 => (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000))
    | 18 => (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))
    | 19 => (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))
    | 20 => (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000))
    | 21 => (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))
    | 22 => (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))
    | 23 => (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000))
    | 24 => (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))
    | 25 => (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))
    | _ => (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (19238061459 / 1000000000000) (19238061668 / 1000000000000)
      | 1 => orderedInterval (-152994438 / 1000000000000) (-152993624 / 1000000000000)
      | 2 => orderedInterval (305041058 / 1000000000000) (305041591 / 1000000000000)
      | 3 => orderedInterval (6246888847 / 1000000000000) (6246903293 / 1000000000000)
      | 4 => orderedInterval (3280918872 / 1000000000000) (3280918998 / 1000000000000)
      | 5 => orderedInterval (3769648201 / 1000000000000) (3769648243 / 1000000000000)
      | 6 => orderedInterval (-968502404 / 1000000000000) (-968502349 / 1000000000000)
      | 7 => orderedInterval (-3576477586 / 1000000000000) (-3576477560 / 1000000000000)
      | _ => orderedInterval (2932039629 / 1000000000000) (2932039690 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1209287046 / 1000000000000) (-1209286819 / 1000000000000)
      | 1 => orderedInterval (4091612122 / 1000000000000) (4091612605 / 1000000000000)
      | 2 => orderedInterval (2270509029 / 1000000000000) (2270509809 / 1000000000000)
      | 3 => orderedInterval (9667556713 / 1000000000000) (9667589788 / 1000000000000)
      | 4 => orderedInterval (-1371020474 / 1000000000000) (-1371020279 / 1000000000000)
      | 5 => orderedInterval (893789825 / 1000000000000) (893789888 / 1000000000000)
      | 6 => orderedInterval (-8828742775 / 1000000000000) (-8828742724 / 1000000000000)
      | 7 => orderedInterval (-5046208824 / 1000000000000) (-5046208800 / 1000000000000)
      | _ => orderedInterval (16050700895 / 1000000000000) (16050700979 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17766501625 / 1000000000000) (-17766501374 / 1000000000000)
      | 1 => orderedInterval (-5154493345 / 1000000000000) (-5154493040 / 1000000000000)
      | 2 => orderedInterval (-2544813257 / 1000000000000) (-2544812111 / 1000000000000)
      | 3 => orderedInterval (-21168649319 / 1000000000000) (-21168573422 / 1000000000000)
      | 4 => orderedInterval (-6080674754 / 1000000000000) (-6080674450 / 1000000000000)
      | 5 => orderedInterval (-8089547538 / 1000000000000) (-8089547443 / 1000000000000)
      | 6 => orderedInterval (569667345 / 1000000000000) (569667394 / 1000000000000)
      | 7 => orderedInterval (2500485564 / 1000000000000) (2500485588 / 1000000000000)
      | _ => orderedInterval (-9000436112 / 1000000000000) (-9000435988 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (951376858 / 1000000000000) (951377136 / 1000000000000)
      | 1 => orderedInterval (-7744083343 / 1000000000000) (-7744083129 / 1000000000000)
      | 2 => orderedInterval (-6802960835 / 1000000000000) (-6802959150 / 1000000000000)
      | 3 => orderedInterval (-41890859931 / 1000000000000) (-41890686098 / 1000000000000)
      | 4 => orderedInterval (4270341812 / 1000000000000) (4270342289 / 1000000000000)
      | 5 => orderedInterval (-1225449314 / 1000000000000) (-1225449168 / 1000000000000)
      | 6 => orderedInterval (8774620448 / 1000000000000) (8774620495 / 1000000000000)
      | 7 => orderedInterval (5113509729 / 1000000000000) (5113509753 / 1000000000000)
      | _ => orderedInterval (-33959536288 / 1000000000000) (-33959536097 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15918362859 / 1000000000000) (15918363172 / 1000000000000)
      | 1 => orderedInterval (14321669037 / 1000000000000) (14321669220 / 1000000000000)
      | 2 => orderedInterval (12830866035 / 1000000000000) (12830868524 / 1000000000000)
      | 3 => orderedInterval (93097863303 / 1000000000000) (93098262279 / 1000000000000)
      | 4 => orderedInterval (7198255525 / 1000000000000) (7198256281 / 1000000000000)
      | 5 => orderedInterval (19684760098 / 1000000000000) (19684760330 / 1000000000000)
      | 6 => orderedInterval (-932713651 / 1000000000000) (-932713604 / 1000000000000)
      | 7 => orderedInterval (-2439588269 / 1000000000000) (-2439588243 / 1000000000000)
      | _ => orderedInterval (27207462123 / 1000000000000) (27207462430 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (31074623638 / 1000000000000) (31074639950 / 1000000000000)
    | 1 => orderedInterval (16518909465 / 1000000000000) (16518944447 / 1000000000000)
    | 2 => orderedInterval (-66734963041 / 1000000000000) (-66734884846 / 1000000000000)
    | 3 => orderedInterval (-72513040864 / 1000000000000) (-72512863969 / 1000000000000)
    | _ => orderedInterval (186886937060 / 1000000000000) (186887340389 / 1000000000000)

theorem compactCertificate342_stateChecks0 :
    compactCertificate342.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (429 / 2)) (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (631998916649529 / 4000000000000)) (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (204375464407257 / 800000000000)) (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks1 :
    compactCertificate342.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (184415707650603 / 4000000000000)) (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (495366530964591 / 4000000000000)) (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1345016494082547 / 4000000000000)) (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks2 :
    compactCertificate342.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (990733061929611 / 4000000000000)) (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1697637988120503 / 4000000000000)) (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250472458455077 / 4000000000000)) (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks3 :
    compactCertificate342.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1918546324694571 / 4000000000000)) (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1107673237015059 / 4000000000000)) (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1965585596891631 / 4000000000000)) (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks4 :
    compactCertificate342.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1836505033673739 / 4000000000000)) (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1310616648756987 / 4000000000000)) (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1486099592893773 / 4000000000000)) (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks5 :
    compactCertificate342.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1238954906883837 / 4000000000000)) (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1094654233964577 / 4000000000000)) (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (317273463201123 / 800000000000)) (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks6 :
    compactCertificate342.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (877595096401881 / 4000000000000)) (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (743947082319441 / 4000000000000)) (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (465527541544923 / 4000000000000)) (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks7 :
    compactCertificate342.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (250362260117541 / 4000000000000)) (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (679782238615623 / 4000000000000)) (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (928184530458471 / 4000000000000)) (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_stateChecks8 :
    compactCertificate342.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (392472458455077 / 4000000000000)) (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1595378754200517 / 4000000000000)) (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1065639071471403 / 4000000000000)) (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_states : ∀ j,
    BesselStateValid (compactCertificate342.point j) (compactCertificate342.state j) :=
  compactCertificate342.statesValid_of_checks3 compactCertificate342_stateChecks0
    compactCertificate342_stateChecks1 compactCertificate342_stateChecks2
    compactCertificate342_stateChecks3 compactCertificate342_stateChecks4
    compactCertificate342_stateChecks5 compactCertificate342_stateChecks6
    compactCertificate342_stateChecks7 compactCertificate342_stateChecks8

theorem compactCertificate342_chunkChecks0_0 :
    compactCertificate342.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (429 / 2) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (631998916649529 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (204375464407257 / 800000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000)))) (orderedInterval (19238061459 / 1000000000000) (19238061668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (184415707650603 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (495366530964591 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1345016494082547 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000)))) (orderedInterval (-152994438 / 1000000000000) (-152993624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (990733061929611 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1697637988120503 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1250472458455077 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000)))) (orderedInterval (305041058 / 1000000000000) (305041591 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks0_1 :
    compactCertificate342.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1918546324694571 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1107673237015059 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1965585596891631 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000)))) (orderedInterval (6246888847 / 1000000000000) (6246903293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1836505033673739 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1310616648756987 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1486099592893773 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000)))) (orderedInterval (3280918872 / 1000000000000) (3280918998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1238954906883837 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1094654233964577 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (317273463201123 / 800000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000)))) (orderedInterval (3769648201 / 1000000000000) (3769648243 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks0_2 :
    compactCertificate342.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (877595096401881 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (743947082319441 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (465527541544923 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000)))) (orderedInterval (-968502404 / 1000000000000) (-968502349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (250362260117541 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (679782238615623 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (928184530458471 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000)))) (orderedInterval (-3576477586 / 1000000000000) (-3576477560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (392472458455077 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1595378754200517 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1065639071471403 / 4000000000000) 0 (IntervalRat.scale (429 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000)))) (orderedInterval (2932039629 / 1000000000000) (2932039690 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks0 :
    compactCertificate342.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate342.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate342_chunkChecks0_0
    compactCertificate342_chunkChecks0_1 compactCertificate342_chunkChecks0_2

theorem compactCertificate342_chunkChecks1_0 :
    compactCertificate342.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (429 / 2) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (631998916649529 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (204375464407257 / 800000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000)))) (orderedInterval (-1209287046 / 1000000000000) (-1209286819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (184415707650603 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (495366530964591 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1345016494082547 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000)))) (orderedInterval (4091612122 / 1000000000000) (4091612605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (990733061929611 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1697637988120503 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1250472458455077 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000)))) (orderedInterval (2270509029 / 1000000000000) (2270509809 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks1_1 :
    compactCertificate342.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1918546324694571 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1107673237015059 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1965585596891631 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000)))) (orderedInterval (9667556713 / 1000000000000) (9667589788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1836505033673739 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1310616648756987 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1486099592893773 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000)))) (orderedInterval (-1371020474 / 1000000000000) (-1371020279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1238954906883837 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1094654233964577 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (317273463201123 / 800000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000)))) (orderedInterval (893789825 / 1000000000000) (893789888 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks1_2 :
    compactCertificate342.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (877595096401881 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (743947082319441 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (465527541544923 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000)))) (orderedInterval (-8828742775 / 1000000000000) (-8828742724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (250362260117541 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (679782238615623 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (928184530458471 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000)))) (orderedInterval (-5046208824 / 1000000000000) (-5046208800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (392472458455077 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1595378754200517 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1065639071471403 / 4000000000000) 1 (IntervalRat.scale (429 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000)))) (orderedInterval (16050700895 / 1000000000000) (16050700979 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks1 :
    compactCertificate342.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate342.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate342_chunkChecks1_0
    compactCertificate342_chunkChecks1_1 compactCertificate342_chunkChecks1_2

theorem compactCertificate342_chunkChecks2_0 :
    compactCertificate342.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (429 / 2) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (631998916649529 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (204375464407257 / 800000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000)))) (orderedInterval (-17766501625 / 1000000000000) (-17766501374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (184415707650603 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (495366530964591 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1345016494082547 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000)))) (orderedInterval (-5154493345 / 1000000000000) (-5154493040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (990733061929611 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1697637988120503 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1250472458455077 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000)))) (orderedInterval (-2544813257 / 1000000000000) (-2544812111 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks2_1 :
    compactCertificate342.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1918546324694571 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1107673237015059 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1965585596891631 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000)))) (orderedInterval (-21168649319 / 1000000000000) (-21168573422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1836505033673739 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1310616648756987 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1486099592893773 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000)))) (orderedInterval (-6080674754 / 1000000000000) (-6080674450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1238954906883837 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1094654233964577 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (317273463201123 / 800000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000)))) (orderedInterval (-8089547538 / 1000000000000) (-8089547443 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks2_2 :
    compactCertificate342.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (877595096401881 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (743947082319441 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (465527541544923 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000)))) (orderedInterval (569667345 / 1000000000000) (569667394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (250362260117541 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (679782238615623 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (928184530458471 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000)))) (orderedInterval (2500485564 / 1000000000000) (2500485588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (392472458455077 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1595378754200517 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1065639071471403 / 4000000000000) 2 (IntervalRat.scale (429 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000)))) (orderedInterval (-9000436112 / 1000000000000) (-9000435988 / 1000000000000))) = true
  rfl'

theorem compactCertificate342_chunkChecks2 :
    compactCertificate342.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate342.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate342_chunkChecks2_0
    compactCertificate342_chunkChecks2_1 compactCertificate342_chunkChecks2_2

theorem compactCertificate342_chunkChecks3_0 :
    compactCertificate342.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (429 / 2) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (631998916649529 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (204375464407257 / 800000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000)))) (orderedInterval (951376858 / 1000000000000) (951377136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (184415707650603 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (495366530964591 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1345016494082547 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000)))) (orderedInterval (-7744083343 / 1000000000000) (-7744083129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (990733061929611 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1697637988120503 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1250472458455077 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000)))) (orderedInterval (-6802960835 / 1000000000000) (-6802959150 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate342_chunkChecks3_1 :
    compactCertificate342.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1918546324694571 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1107673237015059 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1965585596891631 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000)))) (orderedInterval (-41890859931 / 1000000000000) (-41890686098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1836505033673739 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1310616648756987 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1486099592893773 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000)))) (orderedInterval (4270341812 / 1000000000000) (4270342289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1238954906883837 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1094654233964577 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (317273463201123 / 800000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000)))) (orderedInterval (-1225449314 / 1000000000000) (-1225449168 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate342_chunkChecks3_2 :
    compactCertificate342.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (877595096401881 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (743947082319441 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (465527541544923 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000)))) (orderedInterval (8774620448 / 1000000000000) (8774620495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (250362260117541 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (679782238615623 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (928184530458471 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000)))) (orderedInterval (5113509729 / 1000000000000) (5113509753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (392472458455077 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1595378754200517 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1065639071471403 / 4000000000000) 3 (IntervalRat.scale (429 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000)))) (orderedInterval (-33959536288 / 1000000000000) (-33959536097 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate342_chunkChecks3 :
    compactCertificate342.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate342.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate342_chunkChecks3_0
    compactCertificate342_chunkChecks3_1 compactCertificate342_chunkChecks3_2

theorem compactCertificate342_chunkChecks4_0 :
    compactCertificate342.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (429 / 2) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (54278562155 / 1000000000000) (54278562403 / 1000000000000), orderedInterval (-4790649643 / 1000000000000) (-4790649395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (631998916649529 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (62907932566 / 1000000000000) (62907932887 / 1000000000000), orderedInterval (-8673654866 / 1000000000000) (-8673654545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (204375464407257 / 800000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48776154178 / 1000000000000) (-48776152615 / 1000000000000), orderedInterval (10718275770 / 1000000000000) (10718277332 / 1000000000000)))) (orderedInterval (15918362859 / 1000000000000) (15918363172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (184415707650603 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27620284745 / 1000000000000) (27620285051 / 1000000000000), orderedInterval (-114519493555 / 1000000000000) (-114519493249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (495366530964591 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61748167637 / 1000000000000) (-61748146165 / 1000000000000), orderedInterval (36687462104 / 1000000000000) (36687483576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1345016494082547 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33777066032 / 1000000000000) (-33777066031 / 1000000000000), orderedInterval (-27379305526 / 1000000000000) (-27379305525 / 1000000000000)))) (orderedInterval (14321669037 / 1000000000000) (14321669220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (990733061929611 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14124636201 / 1000000000000) (-14124636200 / 1000000000000), orderedInterval (-48662316929 / 1000000000000) (-48662316928 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1697637988120503 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34150772615 / 1000000000000) (-34150772613 / 1000000000000), orderedInterval (-18228241658 / 1000000000000) (-18228241656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1250472458455077 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30962618503 / 1000000000000) (-30962596979 / 1000000000000), orderedInterval (32878318146 / 1000000000000) (32878339669 / 1000000000000)))) (orderedInterval (12830866035 / 1000000000000) (12830868524 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate342_chunkChecks4_1 :
    compactCertificate342.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1918546324694571 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8729244790 / 1000000000000) (8729244804 / 1000000000000), orderedInterval (-35379950023 / 1000000000000) (-35379950008 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1107673237015059 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45395856778 / 1000000000000) (45395856779 / 1000000000000), orderedInterval (15350387464 / 1000000000000) (15350387465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1965585596891631 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31194703275 / 1000000000000) (31194804277 / 1000000000000), orderedInterval (-17987818136 / 1000000000000) (-17987717135 / 1000000000000)))) (orderedInterval (93097863303 / 1000000000000) (93098262279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1836505033673739 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35204244352 / 1000000000000) (35204244355 / 1000000000000), orderedInterval (12096335217 / 1000000000000) (12096335221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1310616648756987 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43630695096 / 1000000000000) (43630696132 / 1000000000000), orderedInterval (-6337369863 / 1000000000000) (-6337368827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1486099592893773 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41374625280 / 1000000000000) (41374625623 / 1000000000000), orderedInterval (-1348253350 / 1000000000000) (-1348253007 / 1000000000000)))) (orderedInterval (7198255525 / 1000000000000) (7198256281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1238954906883837 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494130466 / 1000000000000) (21494131890 / 1000000000000), orderedInterval (-39951464278 / 1000000000000) (-39951462855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1094654233964577 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43619946506 / 1000000000000) (-43619946505 / 1000000000000), orderedInterval (-20501461488 / 1000000000000) (-20501461487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (317273463201123 / 800000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40041341161 / 1000000000000) (40041341331 / 1000000000000), orderedInterval (1333847092 / 1000000000000) (1333847262 / 1000000000000)))) (orderedInterval (19684760098 / 1000000000000) (19684760330 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate342_chunkChecks4_2 :
    compactCertificate342.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (877595096401881 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14477870606 / 1000000000000) (14477870607 / 1000000000000), orderedInterval (51852010551 / 1000000000000) (51852010552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (743947082319441 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57819888322 / 1000000000000) (-57819888315 / 1000000000000), orderedInterval (-8776476630 / 1000000000000) (-8776476624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (465527541544923 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59167175266 / 1000000000000) (-59167175265 / 1000000000000), orderedInterval (-44122882912 / 1000000000000) (-44122882911 / 1000000000000)))) (orderedInterval (-932713651 / 1000000000000) (-932713604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (250362260117541 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52033632535 / 1000000000000) (52033632536 / 1000000000000), orderedInterval (85977824149 / 1000000000000) (85977824150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (679782238615623 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54101119953 / 1000000000000) (54101119954 / 1000000000000), orderedInterval (28460429458 / 1000000000000) (28460429459 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (928184530458471 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18114643626 / 1000000000000) (18114643627 / 1000000000000), orderedInterval (49107378978 / 1000000000000) (49107378979 / 1000000000000)))) (orderedInterval (-2439588269 / 1000000000000) (-2439588243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (392472458455077 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80414343986 / 1000000000000) (-80414343972 / 1000000000000), orderedInterval (-4253885933 / 1000000000000) (-4253885920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1595378754200517 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24098989822 / 1000000000000) (-24098989821 / 1000000000000), orderedInterval (-31835109005 / 1000000000000) (-31835109004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1065639071471403 / 4000000000000) 4 (IntervalRat.scale (429 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7755316526 / 1000000000000) (-7755316525 / 1000000000000), orderedInterval (-48250186643 / 1000000000000) (-48250186642 / 1000000000000)))) (orderedInterval (27207462123 / 1000000000000) (27207462430 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate342_chunkChecks4 :
    compactCertificate342.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate342.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate342_chunkChecks4_0
    compactCertificate342_chunkChecks4_1 compactCertificate342_chunkChecks4_2

theorem compactCertificate342_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate342.chunkCheck r b = true :=
  compactCertificate342.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate342_chunkChecks0
    · exact compactCertificate342_chunkChecks1
    · exact compactCertificate342_chunkChecks2
    · exact compactCertificate342_chunkChecks3
    · exact compactCertificate342_chunkChecks4)

theorem compactCertificate342_coefficient0 :
    compactCertificate342.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate342_coefficient1 :
    compactCertificate342.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate342_coefficient2 :
    compactCertificate342.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate342_coefficient3 :
    compactCertificate342.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate342_coefficient4 :
    compactCertificate342.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate342_coefficients : ∀ r : Fin 5,
    compactCertificate342.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate342_coefficient0
  · exact compactCertificate342_coefficient1
  · exact compactCertificate342_coefficient2
  · exact compactCertificate342_coefficient3
  · exact compactCertificate342_coefficient4

theorem compactCertificate342_lower : (1 : ℚ) ≤ compactCertificate342.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate342, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate342_proves {t : ℝ} (ht : t ∈ compactCertificate342.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate342.proves compactCertificate342_states compactCertificate342_chunks
    compactCertificate342_coefficients compactCertificate342_lower ht

end Erdos232
