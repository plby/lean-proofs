/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate366 : CompactCertificate where
  left := 237
  right := 238
  center := 475 / 2
  grid := fun i =>
    match i.val with
    | 0 => 76
    | 1 => 56
    | 2 => 90
    | 3 => 16
    | 4 => 44
    | 5 => 119
    | 6 => 87
    | 7 => 150
    | 8 => 110
    | 9 => 169
    | 10 => 98
    | 11 => 173
    | 12 => 162
    | 13 => 116
    | 14 => 131
    | 15 => 109
    | 16 => 96
    | 17 => 140
    | 18 => 77
    | 19 => 66
    | 20 => 41
    | 21 => 22
    | 22 => 60
    | 23 => 82
    | 24 => 35
    | 25 => 141
    | _ => 94
  point := fun i =>
    match i.val with
    | 0 => 475 / 2
    | 1 => 27990628010119 / 160000000000
    | 2 => 9051593994727 / 32000000000
    | 3 => 8167595443733 / 160000000000
    | 4 => 21939310229201 / 160000000000
    | 5 => 59569495075917 / 160000000000
    | 6 => 43878620458421 / 160000000000
    | 7 => 75186764042633 / 160000000000
    | 8 => 55382230094747 / 160000000000
    | 9 => 84970583144981 / 160000000000
    | 10 => 49057789051949 / 160000000000
    | 11 => 87053907554641 / 160000000000
    | 12 => 81337052773429 / 160000000000
    | 13 => 58045958802757 / 160000000000
    | 14 => 65817930687603 / 160000000000
    | 15 => 54872128743107 / 160000000000
    | 16 => 48481189849247 / 160000000000
    | 17 => 14051738463453 / 32000000000
    | 18 => 38867848092391 / 160000000000
    | 19 => 32948705277551 / 160000000000
    | 20 => 20617769905253 / 160000000000
    | 21 => 11088305226651 / 160000000000
    | 22 => 30106905672953 / 160000000000
    | 23 => 41108405777881 / 160000000000
    | 24 => 17382230094747 / 160000000000
    | 25 => 70657800302587 / 160000000000
    | _ => 47196136032533 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))
    | 1 => (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))
    | 2 => (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000))
    | 3 => (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))
    | 4 => (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))
    | 5 => (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000))
    | 6 => (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))
    | 7 => (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))
    | 8 => (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000))
    | 9 => (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))
    | 10 => (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))
    | 11 => (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000))
    | 12 => (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))
    | 13 => (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))
    | 14 => (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000))
    | 15 => (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))
    | 16 => (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))
    | 17 => (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000))
    | 18 => (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))
    | 19 => (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))
    | 20 => (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000))
    | 21 => (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))
    | 22 => (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))
    | 23 => (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000))
    | 24 => (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))
    | 25 => (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))
    | _ => (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7332379563 / 1000000000000) (-7332378845 / 1000000000000)
      | 1 => orderedInterval (-4020445598 / 1000000000000) (-4020444413 / 1000000000000)
      | 2 => orderedInterval (1591292273 / 1000000000000) (1591292315 / 1000000000000)
      | 3 => orderedInterval (-1427303476 / 1000000000000) (-1427303283 / 1000000000000)
      | 4 => orderedInterval (-2999513032 / 1000000000000) (-2999509104 / 1000000000000)
      | 5 => orderedInterval (-2524272121 / 1000000000000) (-2524265762 / 1000000000000)
      | 6 => orderedInterval (8111479411 / 1000000000000) (8111480378 / 1000000000000)
      | 7 => orderedInterval (-2430867685 / 1000000000000) (-2430867656 / 1000000000000)
      | _ => orderedInterval (-5228945500 / 1000000000000) (-5228945268 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (20710181157 / 1000000000000) (20710181877 / 1000000000000)
      | 1 => orderedInterval (4723818903 / 1000000000000) (4723820729 / 1000000000000)
      | 2 => orderedInterval (-1601399028 / 1000000000000) (-1601398949 / 1000000000000)
      | 3 => orderedInterval (10029483527 / 1000000000000) (10029483857 / 1000000000000)
      | 4 => orderedInterval (2934379856 / 1000000000000) (2934385859 / 1000000000000)
      | 5 => orderedInterval (3579746416 / 1000000000000) (3579754533 / 1000000000000)
      | 6 => orderedInterval (-5002464919 / 1000000000000) (-5002464030 / 1000000000000)
      | 7 => orderedInterval (-5330259993 / 1000000000000) (-5330259967 / 1000000000000)
      | _ => orderedInterval (-5069877333 / 1000000000000) (-5069876987 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6277908164 / 1000000000000) (6277908889 / 1000000000000)
      | 1 => orderedInterval (5251915473 / 1000000000000) (5251918326 / 1000000000000)
      | 2 => orderedInterval (-4412424180 / 1000000000000) (-4412424029 / 1000000000000)
      | 3 => orderedInterval (3082640144 / 1000000000000) (3082640754 / 1000000000000)
      | 4 => orderedInterval (7202304510 / 1000000000000) (7202313710 / 1000000000000)
      | 5 => orderedInterval (4175426518 / 1000000000000) (4175436915 / 1000000000000)
      | 6 => orderedInterval (-9199904655 / 1000000000000) (-9199903829 / 1000000000000)
      | 7 => orderedInterval (966470033 / 1000000000000) (966470059 / 1000000000000)
      | _ => orderedInterval (11584443783 / 1000000000000) (11584444366 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-21406920943 / 1000000000000) (-21406920215 / 1000000000000)
      | 1 => orderedInterval (-8733116900 / 1000000000000) (-8733112437 / 1000000000000)
      | 2 => orderedInterval (6879624445 / 1000000000000) (6879624738 / 1000000000000)
      | 3 => orderedInterval (-36730851786 / 1000000000000) (-36730850583 / 1000000000000)
      | 4 => orderedInterval (-4056831991 / 1000000000000) (-4056817926 / 1000000000000)
      | 5 => orderedInterval (-8975097349 / 1000000000000) (-8975084072 / 1000000000000)
      | 6 => orderedInterval (4002240857 / 1000000000000) (4002241627 / 1000000000000)
      | 7 => orderedInterval (5412254194 / 1000000000000) (5412254221 / 1000000000000)
      | _ => orderedInterval (-1753353282 / 1000000000000) (-1753352253 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4858101896 / 1000000000000) (-4858101160 / 1000000000000)
      | 1 => orderedInterval (-12184208110 / 1000000000000) (-12184201102 / 1000000000000)
      | 2 => orderedInterval (13396687751 / 1000000000000) (13396688319 / 1000000000000)
      | 3 => orderedInterval (-12869959632 / 1000000000000) (-12869957136 / 1000000000000)
      | 4 => orderedInterval (-17906916033 / 1000000000000) (-17906894462 / 1000000000000)
      | 5 => orderedInterval (-6732055661 / 1000000000000) (-6732038643 / 1000000000000)
      | 6 => orderedInterval (9579412656 / 1000000000000) (9579413382 / 1000000000000)
      | 7 => orderedInterval (-816969124 / 1000000000000) (-816969095 / 1000000000000)
      | _ => orderedInterval (-28898052020 / 1000000000000) (-28898050162 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16260955291 / 1000000000000) (-16260941638 / 1000000000000)
    | 1 => orderedInterval (24973608586 / 1000000000000) (24973626922 / 1000000000000)
    | 2 => orderedInterval (24928779790 / 1000000000000) (24928805161 / 1000000000000)
    | 3 => orderedInterval (-65362052755 / 1000000000000) (-65362016900 / 1000000000000)
    | _ => orderedInterval (-61290162069 / 1000000000000) (-61290110059 / 1000000000000)

theorem compactCertificate366_stateChecks0 :
    compactCertificate366.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (475 / 2)) (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (27990628010119 / 160000000000)) (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (9051593994727 / 32000000000)) (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks1 :
    compactCertificate366.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (8167595443733 / 160000000000)) (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (21939310229201 / 160000000000)) (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (59569495075917 / 160000000000)) (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks2 :
    compactCertificate366.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (43878620458421 / 160000000000)) (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (75186764042633 / 160000000000)) (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (55382230094747 / 160000000000)) (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks3 :
    compactCertificate366.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (84970583144981 / 160000000000)) (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (49057789051949 / 160000000000)) (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (87053907554641 / 160000000000)) (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks4 :
    compactCertificate366.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (81337052773429 / 160000000000)) (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (58045958802757 / 160000000000)) (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (65817930687603 / 160000000000)) (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks5 :
    compactCertificate366.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (54872128743107 / 160000000000)) (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (48481189849247 / 160000000000)) (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (14051738463453 / 32000000000)) (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks6 :
    compactCertificate366.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (38867848092391 / 160000000000)) (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (32948705277551 / 160000000000)) (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (20617769905253 / 160000000000)) (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks7 :
    compactCertificate366.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (11088305226651 / 160000000000)) (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (30106905672953 / 160000000000)) (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (41108405777881 / 160000000000)) (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_stateChecks8 :
    compactCertificate366.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (17382230094747 / 160000000000)) (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (70657800302587 / 160000000000)) (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (47196136032533 / 160000000000)) (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_states : ∀ j,
    BesselStateValid (compactCertificate366.point j) (compactCertificate366.state j) :=
  compactCertificate366.statesValid_of_checks3 compactCertificate366_stateChecks0
    compactCertificate366_stateChecks1 compactCertificate366_stateChecks2
    compactCertificate366_stateChecks3 compactCertificate366_stateChecks4
    compactCertificate366_stateChecks5 compactCertificate366_stateChecks6
    compactCertificate366_stateChecks7 compactCertificate366_stateChecks8

theorem compactCertificate366_chunkChecks0_0 :
    compactCertificate366.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (475 / 2) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (27990628010119 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (9051593994727 / 32000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000)))) (orderedInterval (-7332379563 / 1000000000000) (-7332378845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (8167595443733 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (21939310229201 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (59569495075917 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000)))) (orderedInterval (-4020445598 / 1000000000000) (-4020444413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (43878620458421 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (75186764042633 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (55382230094747 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000)))) (orderedInterval (1591292273 / 1000000000000) (1591292315 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks0_1 :
    compactCertificate366.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (84970583144981 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (49057789051949 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (87053907554641 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000)))) (orderedInterval (-1427303476 / 1000000000000) (-1427303283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (81337052773429 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (58045958802757 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (65817930687603 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000)))) (orderedInterval (-2999513032 / 1000000000000) (-2999509104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (54872128743107 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (48481189849247 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (14051738463453 / 32000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000)))) (orderedInterval (-2524272121 / 1000000000000) (-2524265762 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks0_2 :
    compactCertificate366.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (38867848092391 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (32948705277551 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (20617769905253 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000)))) (orderedInterval (8111479411 / 1000000000000) (8111480378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (11088305226651 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (30106905672953 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (41108405777881 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000)))) (orderedInterval (-2430867685 / 1000000000000) (-2430867656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (17382230094747 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (70657800302587 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (47196136032533 / 160000000000) 0 (IntervalRat.scale (475 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000)))) (orderedInterval (-5228945500 / 1000000000000) (-5228945268 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks0 :
    compactCertificate366.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate366.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate366_chunkChecks0_0
    compactCertificate366_chunkChecks0_1 compactCertificate366_chunkChecks0_2

theorem compactCertificate366_chunkChecks1_0 :
    compactCertificate366.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (475 / 2) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (27990628010119 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (9051593994727 / 32000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000)))) (orderedInterval (20710181157 / 1000000000000) (20710181877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (8167595443733 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (21939310229201 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (59569495075917 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000)))) (orderedInterval (4723818903 / 1000000000000) (4723820729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (43878620458421 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (75186764042633 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (55382230094747 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000)))) (orderedInterval (-1601399028 / 1000000000000) (-1601398949 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks1_1 :
    compactCertificate366.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (84970583144981 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (49057789051949 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (87053907554641 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000)))) (orderedInterval (10029483527 / 1000000000000) (10029483857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (81337052773429 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (58045958802757 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (65817930687603 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000)))) (orderedInterval (2934379856 / 1000000000000) (2934385859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (54872128743107 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (48481189849247 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (14051738463453 / 32000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000)))) (orderedInterval (3579746416 / 1000000000000) (3579754533 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks1_2 :
    compactCertificate366.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (38867848092391 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (32948705277551 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (20617769905253 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000)))) (orderedInterval (-5002464919 / 1000000000000) (-5002464030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (11088305226651 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (30106905672953 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (41108405777881 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000)))) (orderedInterval (-5330259993 / 1000000000000) (-5330259967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (17382230094747 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (70657800302587 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (47196136032533 / 160000000000) 1 (IntervalRat.scale (475 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000)))) (orderedInterval (-5069877333 / 1000000000000) (-5069876987 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks1 :
    compactCertificate366.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate366.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate366_chunkChecks1_0
    compactCertificate366_chunkChecks1_1 compactCertificate366_chunkChecks1_2

theorem compactCertificate366_chunkChecks2_0 :
    compactCertificate366.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (475 / 2) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (27990628010119 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (9051593994727 / 32000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000)))) (orderedInterval (6277908164 / 1000000000000) (6277908889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (8167595443733 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (21939310229201 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (59569495075917 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000)))) (orderedInterval (5251915473 / 1000000000000) (5251918326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (43878620458421 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (75186764042633 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (55382230094747 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000)))) (orderedInterval (-4412424180 / 1000000000000) (-4412424029 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks2_1 :
    compactCertificate366.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (84970583144981 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (49057789051949 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (87053907554641 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000)))) (orderedInterval (3082640144 / 1000000000000) (3082640754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (81337052773429 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (58045958802757 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (65817930687603 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000)))) (orderedInterval (7202304510 / 1000000000000) (7202313710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (54872128743107 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (48481189849247 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (14051738463453 / 32000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000)))) (orderedInterval (4175426518 / 1000000000000) (4175436915 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks2_2 :
    compactCertificate366.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (38867848092391 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (32948705277551 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (20617769905253 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000)))) (orderedInterval (-9199904655 / 1000000000000) (-9199903829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (11088305226651 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (30106905672953 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (41108405777881 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000)))) (orderedInterval (966470033 / 1000000000000) (966470059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (17382230094747 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (70657800302587 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (47196136032533 / 160000000000) 2 (IntervalRat.scale (475 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000)))) (orderedInterval (11584443783 / 1000000000000) (11584444366 / 1000000000000))) = true
  rfl'

theorem compactCertificate366_chunkChecks2 :
    compactCertificate366.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate366.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate366_chunkChecks2_0
    compactCertificate366_chunkChecks2_1 compactCertificate366_chunkChecks2_2

theorem compactCertificate366_chunkChecks3_0 :
    compactCertificate366.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (475 / 2) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (27990628010119 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (9051593994727 / 32000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000)))) (orderedInterval (-21406920943 / 1000000000000) (-21406920215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (8167595443733 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (21939310229201 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (59569495075917 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000)))) (orderedInterval (-8733116900 / 1000000000000) (-8733112437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (43878620458421 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (75186764042633 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (55382230094747 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000)))) (orderedInterval (6879624445 / 1000000000000) (6879624738 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate366_chunkChecks3_1 :
    compactCertificate366.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (84970583144981 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (49057789051949 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (87053907554641 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000)))) (orderedInterval (-36730851786 / 1000000000000) (-36730850583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (81337052773429 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (58045958802757 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (65817930687603 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000)))) (orderedInterval (-4056831991 / 1000000000000) (-4056817926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (54872128743107 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (48481189849247 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (14051738463453 / 32000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000)))) (orderedInterval (-8975097349 / 1000000000000) (-8975084072 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate366_chunkChecks3_2 :
    compactCertificate366.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (38867848092391 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (32948705277551 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (20617769905253 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000)))) (orderedInterval (4002240857 / 1000000000000) (4002241627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (11088305226651 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (30106905672953 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (41108405777881 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000)))) (orderedInterval (5412254194 / 1000000000000) (5412254221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (17382230094747 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (70657800302587 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (47196136032533 / 160000000000) 3 (IntervalRat.scale (475 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000)))) (orderedInterval (-1753353282 / 1000000000000) (-1753352253 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate366_chunkChecks3 :
    compactCertificate366.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate366.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate366_chunkChecks3_0
    compactCertificate366_chunkChecks3_1 compactCertificate366_chunkChecks3_2

theorem compactCertificate366_chunkChecks4_0 :
    compactCertificate366.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (475 / 2) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23731870914 / 1000000000000) (-23731869149 / 1000000000000), orderedInterval (46064155160 / 1000000000000) (46064156925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (27990628010119 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12166635292 / 1000000000000) (-12166635211 / 1000000000000), orderedInterval (59119728487 / 1000000000000) (59119728568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (9051593994727 / 32000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37277270556 / 1000000000000) (37277270557 / 1000000000000), orderedInterval (29277575080 / 1000000000000) (29277575081 / 1000000000000)))) (orderedInterval (-4858101896 / 1000000000000) (-4858101160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (8167595443733 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (111669631717 / 1000000000000) (111669631738 / 1000000000000), orderedInterval (-439554943 / 1000000000000) (-439554922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (21939310229201 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21750572273 / 1000000000000) (-21750571742 / 1000000000000), orderedInterval (64652577643 / 1000000000000) (64652578174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (59569495075917 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28341073579 / 1000000000000) (28341089569 / 1000000000000), orderedInterval (-30149607055 / 1000000000000) (-30149591065 / 1000000000000)))) (orderedInterval (-12184208110 / 1000000000000) (-12184201102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (43878620458421 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47729509922 / 1000000000000) (-47729509225 / 1000000000000), orderedInterval (6665395758 / 1000000000000) (6665396456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (75186764042633 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18812845851 / 1000000000000) (-18812844948 / 1000000000000), orderedInterval (31655847926 / 1000000000000) (31655848830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (55382230094747 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41833322660 / 1000000000000) (41833322667 / 1000000000000), orderedInterval (9382790303 / 1000000000000) (9382790311 / 1000000000000)))) (orderedInterval (13396687751 / 1000000000000) (13396688319 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate366_chunkChecks4_1 :
    compactCertificate366.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (84970583144981 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27591188017 / 1000000000000) (-27591188016 / 1000000000000), orderedInterval (-20890145063 / 1000000000000) (-20890145062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (49057789051949 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21037947857 / 1000000000000) (-21037946626 / 1000000000000), orderedInterval (40453560128 / 1000000000000) (40453561359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (87053907554641 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33563051949 / 1000000000000) (-33563051898 / 1000000000000), orderedInterval (-6571509569 / 1000000000000) (-6571509518 / 1000000000000)))) (orderedInterval (-12869959632 / 1000000000000) (-12869957136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (81337052773429 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7159553006 / 1000000000000) (7159553007 / 1000000000000), orderedInterval (34649138735 / 1000000000000) (34649138736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (58045958802757 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31539096050 / 1000000000000) (-31539054814 / 1000000000000), orderedInterval (27613147973 / 1000000000000) (27613189208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (65817930687603 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22164734218 / 1000000000000) (-22164734217 / 1000000000000), orderedInterval (-32474057151 / 1000000000000) (-32474057150 / 1000000000000)))) (orderedInterval (-17906916033 / 1000000000000) (-17906894462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (54872128743107 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41540397713 / 1000000000000) (-41540397709 / 1000000000000), orderedInterval (-11371594546 / 1000000000000) (-11371594543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (48481189849247 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37071474001 / 1000000000000) (37071584720 / 1000000000000), orderedInterval (-27018682994 / 1000000000000) (-27018572275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (14051738463453 / 32000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3003688859 / 1000000000000) (3003688860 / 1000000000000), orderedInterval (37953817658 / 1000000000000) (37953817659 / 1000000000000)))) (orderedInterval (-6732055661 / 1000000000000) (-6732038643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate366_chunkChecks4_2 :
    compactCertificate366.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (38867848092391 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49779204431 / 1000000000000) (-49779202582 / 1000000000000), orderedInterval (12047308812 / 1000000000000) (12047310660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (32948705277551 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32798002980 / 1000000000000) (-32797992169 / 1000000000000), orderedInterval (44976629383 / 1000000000000) (44976640194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (20617769905253 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52348012539 / 1000000000000) (-52348012538 / 1000000000000), orderedInterval (-46701463389 / 1000000000000) (-46701463388 / 1000000000000)))) (orderedInterval (9579412656 / 1000000000000) (9579413382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (11088305226651 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79084907597 / 1000000000000) (79084907598 / 1000000000000), orderedInterval (53574350604 / 1000000000000) (53574350605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (30106905672953 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25683524923 / 1000000000000) (25683524924 / 1000000000000), orderedInterval (52120000101 / 1000000000000) (52120000102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (41108405777881 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5061100372 / 1000000000000) (5061100373 / 1000000000000), orderedInterval (49509927033 / 1000000000000) (49509927034 / 1000000000000)))) (orderedInterval (-816969124 / 1000000000000) (-816969095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (17382230094747 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38867325816 / 1000000000000) (38867332369 / 1000000000000), orderedInterval (-66128258634 / 1000000000000) (-66128252082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (70657800302587 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20431187591 / 1000000000000) (20431189143 / 1000000000000), orderedInterval (-32025493504 / 1000000000000) (-32025491952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (47196136032533 / 160000000000) 4 (IntervalRat.scale (475 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20253614528 / 1000000000000) (20253614529 / 1000000000000), orderedInterval (41774792846 / 1000000000000) (41774792847 / 1000000000000)))) (orderedInterval (-28898052020 / 1000000000000) (-28898050162 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate366_chunkChecks4 :
    compactCertificate366.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate366.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate366_chunkChecks4_0
    compactCertificate366_chunkChecks4_1 compactCertificate366_chunkChecks4_2

theorem compactCertificate366_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate366.chunkCheck r b = true :=
  compactCertificate366.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate366_chunkChecks0
    · exact compactCertificate366_chunkChecks1
    · exact compactCertificate366_chunkChecks2
    · exact compactCertificate366_chunkChecks3
    · exact compactCertificate366_chunkChecks4)

theorem compactCertificate366_coefficient0 :
    compactCertificate366.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate366_coefficient1 :
    compactCertificate366.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate366_coefficient2 :
    compactCertificate366.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate366_coefficient3 :
    compactCertificate366.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate366_coefficient4 :
    compactCertificate366.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate366_coefficients : ∀ r : Fin 5,
    compactCertificate366.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate366_coefficient0
  · exact compactCertificate366_coefficient1
  · exact compactCertificate366_coefficient2
  · exact compactCertificate366_coefficient3
  · exact compactCertificate366_coefficient4

theorem compactCertificate366_lower : (1 : ℚ) ≤ compactCertificate366.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate366, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate366_proves {t : ℝ} (ht : t ∈ compactCertificate366.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate366.proves compactCertificate366_states compactCertificate366_chunks
    compactCertificate366_coefficients compactCertificate366_lower ht

end Erdos232
