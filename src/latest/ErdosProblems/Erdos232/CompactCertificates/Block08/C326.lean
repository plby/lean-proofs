/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate326 : CompactCertificate where
  left := 198
  right := 199
  center := 397 / 2
  grid := fun i =>
    match i.val with
    | 0 => 63
    | 1 => 47
    | 2 => 75
    | 3 => 14
    | 4 => 36
    | 5 => 99
    | 6 => 73
    | 7 => 125
    | 8 => 92
    | 9 => 141
    | 10 => 82
    | 11 => 145
    | 12 => 135
    | 13 => 97
    | 14 => 109
    | 15 => 91
    | 16 => 81
    | 17 => 117
    | 18 => 65
    | 19 => 55
    | 20 => 34
    | 21 => 18
    | 22 => 50
    | 23 => 68
    | 24 => 29
    | 25 => 118
    | _ => 79
  point := fun i =>
    match i.val with
    | 0 => 397 / 2
    | 1 => 584856806316697 / 4000000000000
    | 2 => 189130674521401 / 800000000000
    | 3 => 170659757429579 / 4000000000000
    | 4 => 458416113736463 / 4000000000000
    | 5 => 1244688923428371 / 4000000000000
    | 6 => 916832227473323 / 4000000000000
    | 7 => 1571007648680279 / 4000000000000
    | 8 => 1157197123558661 / 4000000000000
    | 9 => 1775437974134603 / 4000000000000
    | 10 => 1025049592295987 / 4000000000000
    | 11 => 1818968489431183 / 4000000000000
    | 12 => 1699516313213227 / 4000000000000
    | 13 => 1212855033931291 / 4000000000000
    | 14 => 1375248341209389 / 4000000000000
    | 15 => 1146538690053341 / 4000000000000
    | 16 => 1013001703692161 / 4000000000000
    | 17 => 293607377367939 / 800000000000
    | 18 => 812133457509433 / 4000000000000
    | 19 => 688454526062513 / 4000000000000
    | 20 => 430802876441339 / 4000000000000
    | 21 => 231687219735813 / 4000000000000
    | 22 => 629075871166439 / 4000000000000
    | 23 => 858949320727303 / 4000000000000
    | 24 => 363197123558661 / 4000000000000
    | 25 => 1476376143164581 / 4000000000000
    | _ => 986150842363979 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))
    | 1 => (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))
    | 2 => (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000))
    | 3 => (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))
    | 4 => (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))
    | 5 => (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000))
    | 6 => (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))
    | 7 => (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))
    | 8 => (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000))
    | 9 => (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))
    | 10 => (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))
    | 11 => (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000))
    | 12 => (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))
    | 13 => (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))
    | 14 => (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000))
    | 15 => (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))
    | 16 => (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))
    | 17 => (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000))
    | 18 => (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))
    | 19 => (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))
    | 20 => (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000))
    | 21 => (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))
    | 22 => (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))
    | 23 => (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000))
    | 24 => (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))
    | 25 => (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))
    | _ => (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-24640451255 / 1000000000000) (-24640451061 / 1000000000000)
      | 1 => orderedInterval (5316863823 / 1000000000000) (5316867878 / 1000000000000)
      | 2 => orderedInterval (1910708835 / 1000000000000) (1910708847 / 1000000000000)
      | 3 => orderedInterval (4736986670 / 1000000000000) (4736987305 / 1000000000000)
      | 4 => orderedInterval (3787283366 / 1000000000000) (3787285643 / 1000000000000)
      | 5 => orderedInterval (-1990494432 / 1000000000000) (-1990494356 / 1000000000000)
      | 6 => orderedInterval (-494875413 / 1000000000000) (-494875239 / 1000000000000)
      | 7 => orderedInterval (-6764160718 / 1000000000000) (-6764159898 / 1000000000000)
      | _ => orderedInterval (-4985278160 / 1000000000000) (-4985261262 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4867343964 / 1000000000000) (-4867343813 / 1000000000000)
      | 1 => orderedInterval (1680037370 / 1000000000000) (1680039688 / 1000000000000)
      | 2 => orderedInterval (2450034088 / 1000000000000) (2450034108 / 1000000000000)
      | 3 => orderedInterval (-9806591588 / 1000000000000) (-9806590473 / 1000000000000)
      | 4 => orderedInterval (-5094580629 / 1000000000000) (-5094577045 / 1000000000000)
      | 5 => orderedInterval (1377765270 / 1000000000000) (1377765371 / 1000000000000)
      | 6 => orderedInterval (11318263129 / 1000000000000) (11318263300 / 1000000000000)
      | 7 => orderedInterval (1119565187 / 1000000000000) (1119565692 / 1000000000000)
      | _ => orderedInterval (3256784259 / 1000000000000) (3256806882 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (26110816739 / 1000000000000) (26110816861 / 1000000000000)
      | 1 => orderedInterval (-7100594766 / 1000000000000) (-7100593401 / 1000000000000)
      | 2 => orderedInterval (-5723673766 / 1000000000000) (-5723673731 / 1000000000000)
      | 3 => orderedInterval (-30213390293 / 1000000000000) (-30213388185 / 1000000000000)
      | 4 => orderedInterval (-10502432049 / 1000000000000) (-10502426372 / 1000000000000)
      | 5 => orderedInterval (3913316041 / 1000000000000) (3913316176 / 1000000000000)
      | 6 => orderedInterval (2445011594 / 1000000000000) (2445011765 / 1000000000000)
      | 7 => orderedInterval (5511991910 / 1000000000000) (5511992347 / 1000000000000)
      | _ => orderedInterval (2592715696 / 1000000000000) (2592746951 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4555791832 / 1000000000000) (4555791934 / 1000000000000)
      | 1 => orderedInterval (-6899769184 / 1000000000000) (-6899768363 / 1000000000000)
      | 2 => orderedInterval (-8114680785 / 1000000000000) (-8114680721 / 1000000000000)
      | 3 => orderedInterval (65662147397 / 1000000000000) (65662151608 / 1000000000000)
      | 4 => orderedInterval (12012145299 / 1000000000000) (12012154297 / 1000000000000)
      | 5 => orderedInterval (1188354719 / 1000000000000) (1188354903 / 1000000000000)
      | 6 => orderedInterval (-11086829721 / 1000000000000) (-11086829549 / 1000000000000)
      | 7 => orderedInterval (-1341874970 / 1000000000000) (-1341874532 / 1000000000000)
      | _ => orderedInterval (2836258894 / 1000000000000) (2836303385 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-28032154184 / 1000000000000) (-28032154094 / 1000000000000)
      | 1 => orderedInterval (15974207663 / 1000000000000) (15974208195 / 1000000000000)
      | 2 => orderedInterval (18683512539 / 1000000000000) (18683512656 / 1000000000000)
      | 3 => orderedInterval (161632148452 / 1000000000000) (161632157244 / 1000000000000)
      | 4 => orderedInterval (32001618584 / 1000000000000) (32001632947 / 1000000000000)
      | 5 => orderedInterval (-8386812672 / 1000000000000) (-8386812418 / 1000000000000)
      | 6 => orderedInterval (-3141211553 / 1000000000000) (-3141211378 / 1000000000000)
      | 7 => orderedInterval (-5887910075 / 1000000000000) (-5887909609 / 1000000000000)
      | _ => orderedInterval (12509965294 / 1000000000000) (12510031328 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-23123417284 / 1000000000000) (-23123392143 / 1000000000000)
    | 1 => orderedInterval (1433933122 / 1000000000000) (1433963710 / 1000000000000)
    | 2 => orderedInterval (-12966238894 / 1000000000000) (-12966197589 / 1000000000000)
    | 3 => orderedInterval (58811543481 / 1000000000000) (58811602962 / 1000000000000)
    | _ => orderedInterval (195353364048 / 1000000000000) (195353454871 / 1000000000000)

theorem compactCertificate326_stateChecks0 :
    compactCertificate326.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (397 / 2)) (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584856806316697 / 4000000000000)) (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (189130674521401 / 800000000000)) (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks1 :
    compactCertificate326.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (170659757429579 / 4000000000000)) (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (458416113736463 / 4000000000000)) (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1244688923428371 / 4000000000000)) (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks2 :
    compactCertificate326.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (916832227473323 / 4000000000000)) (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1571007648680279 / 4000000000000)) (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1157197123558661 / 4000000000000)) (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks3 :
    compactCertificate326.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1775437974134603 / 4000000000000)) (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1025049592295987 / 4000000000000)) (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1818968489431183 / 4000000000000)) (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks4 :
    compactCertificate326.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1699516313213227 / 4000000000000)) (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1212855033931291 / 4000000000000)) (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1375248341209389 / 4000000000000)) (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks5 :
    compactCertificate326.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1146538690053341 / 4000000000000)) (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1013001703692161 / 4000000000000)) (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (293607377367939 / 800000000000)) (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks6 :
    compactCertificate326.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (812133457509433 / 4000000000000)) (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (688454526062513 / 4000000000000)) (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (430802876441339 / 4000000000000)) (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks7 :
    compactCertificate326.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (231687219735813 / 4000000000000)) (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (629075871166439 / 4000000000000)) (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (858949320727303 / 4000000000000)) (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_stateChecks8 :
    compactCertificate326.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (363197123558661 / 4000000000000)) (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1476376143164581 / 4000000000000)) (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (986150842363979 / 4000000000000)) (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_states : ∀ j,
    BesselStateValid (compactCertificate326.point j) (compactCertificate326.state j) :=
  compactCertificate326.statesValid_of_checks3 compactCertificate326_stateChecks0
    compactCertificate326_stateChecks1 compactCertificate326_stateChecks2
    compactCertificate326_stateChecks3 compactCertificate326_stateChecks4
    compactCertificate326_stateChecks5 compactCertificate326_stateChecks6
    compactCertificate326_stateChecks7 compactCertificate326_stateChecks8

theorem compactCertificate326_chunkChecks0_0 :
    compactCertificate326.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (397 / 2) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (584856806316697 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (189130674521401 / 800000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000)))) (orderedInterval (-24640451255 / 1000000000000) (-24640451061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (170659757429579 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (458416113736463 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1244688923428371 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000)))) (orderedInterval (5316863823 / 1000000000000) (5316867878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (916832227473323 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1571007648680279 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1157197123558661 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000)))) (orderedInterval (1910708835 / 1000000000000) (1910708847 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks0_1 :
    compactCertificate326.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1775437974134603 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1025049592295987 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1818968489431183 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000)))) (orderedInterval (4736986670 / 1000000000000) (4736987305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1699516313213227 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1212855033931291 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1375248341209389 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000)))) (orderedInterval (3787283366 / 1000000000000) (3787285643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1146538690053341 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1013001703692161 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (293607377367939 / 800000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000)))) (orderedInterval (-1990494432 / 1000000000000) (-1990494356 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks0_2 :
    compactCertificate326.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (812133457509433 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (688454526062513 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (430802876441339 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000)))) (orderedInterval (-494875413 / 1000000000000) (-494875239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (231687219735813 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (629075871166439 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (858949320727303 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000)))) (orderedInterval (-6764160718 / 1000000000000) (-6764159898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (363197123558661 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1476376143164581 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (986150842363979 / 4000000000000) 0 (IntervalRat.scale (397 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000)))) (orderedInterval (-4985278160 / 1000000000000) (-4985261262 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks0 :
    compactCertificate326.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate326.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate326_chunkChecks0_0
    compactCertificate326_chunkChecks0_1 compactCertificate326_chunkChecks0_2

theorem compactCertificate326_chunkChecks1_0 :
    compactCertificate326.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (397 / 2) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (584856806316697 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (189130674521401 / 800000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000)))) (orderedInterval (-4867343964 / 1000000000000) (-4867343813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (170659757429579 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (458416113736463 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1244688923428371 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000)))) (orderedInterval (1680037370 / 1000000000000) (1680039688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (916832227473323 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1571007648680279 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1157197123558661 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000)))) (orderedInterval (2450034088 / 1000000000000) (2450034108 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks1_1 :
    compactCertificate326.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1775437974134603 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1025049592295987 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1818968489431183 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000)))) (orderedInterval (-9806591588 / 1000000000000) (-9806590473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1699516313213227 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1212855033931291 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1375248341209389 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000)))) (orderedInterval (-5094580629 / 1000000000000) (-5094577045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1146538690053341 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1013001703692161 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (293607377367939 / 800000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000)))) (orderedInterval (1377765270 / 1000000000000) (1377765371 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks1_2 :
    compactCertificate326.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (812133457509433 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (688454526062513 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (430802876441339 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000)))) (orderedInterval (11318263129 / 1000000000000) (11318263300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (231687219735813 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (629075871166439 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (858949320727303 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000)))) (orderedInterval (1119565187 / 1000000000000) (1119565692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (363197123558661 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1476376143164581 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (986150842363979 / 4000000000000) 1 (IntervalRat.scale (397 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000)))) (orderedInterval (3256784259 / 1000000000000) (3256806882 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks1 :
    compactCertificate326.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate326.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate326_chunkChecks1_0
    compactCertificate326_chunkChecks1_1 compactCertificate326_chunkChecks1_2

theorem compactCertificate326_chunkChecks2_0 :
    compactCertificate326.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (397 / 2) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (584856806316697 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (189130674521401 / 800000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000)))) (orderedInterval (26110816739 / 1000000000000) (26110816861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (170659757429579 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (458416113736463 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1244688923428371 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000)))) (orderedInterval (-7100594766 / 1000000000000) (-7100593401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (916832227473323 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1571007648680279 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1157197123558661 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000)))) (orderedInterval (-5723673766 / 1000000000000) (-5723673731 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks2_1 :
    compactCertificate326.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1775437974134603 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1025049592295987 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1818968489431183 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000)))) (orderedInterval (-30213390293 / 1000000000000) (-30213388185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1699516313213227 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1212855033931291 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1375248341209389 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000)))) (orderedInterval (-10502432049 / 1000000000000) (-10502426372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1146538690053341 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1013001703692161 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (293607377367939 / 800000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000)))) (orderedInterval (3913316041 / 1000000000000) (3913316176 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks2_2 :
    compactCertificate326.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (812133457509433 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (688454526062513 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (430802876441339 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000)))) (orderedInterval (2445011594 / 1000000000000) (2445011765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (231687219735813 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (629075871166439 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (858949320727303 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000)))) (orderedInterval (5511991910 / 1000000000000) (5511992347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (363197123558661 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1476376143164581 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (986150842363979 / 4000000000000) 2 (IntervalRat.scale (397 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000)))) (orderedInterval (2592715696 / 1000000000000) (2592746951 / 1000000000000))) = true
  rfl'

theorem compactCertificate326_chunkChecks2 :
    compactCertificate326.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate326.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate326_chunkChecks2_0
    compactCertificate326_chunkChecks2_1 compactCertificate326_chunkChecks2_2

theorem compactCertificate326_chunkChecks3_0 :
    compactCertificate326.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (397 / 2) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (584856806316697 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (189130674521401 / 800000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000)))) (orderedInterval (4555791832 / 1000000000000) (4555791934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (170659757429579 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (458416113736463 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1244688923428371 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000)))) (orderedInterval (-6899769184 / 1000000000000) (-6899768363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (916832227473323 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1571007648680279 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1157197123558661 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000)))) (orderedInterval (-8114680785 / 1000000000000) (-8114680721 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate326_chunkChecks3_1 :
    compactCertificate326.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1775437974134603 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1025049592295987 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1818968489431183 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000)))) (orderedInterval (65662147397 / 1000000000000) (65662151608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1699516313213227 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1212855033931291 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1375248341209389 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000)))) (orderedInterval (12012145299 / 1000000000000) (12012154297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1146538690053341 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1013001703692161 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (293607377367939 / 800000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000)))) (orderedInterval (1188354719 / 1000000000000) (1188354903 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate326_chunkChecks3_2 :
    compactCertificate326.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (812133457509433 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (688454526062513 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (430802876441339 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000)))) (orderedInterval (-11086829721 / 1000000000000) (-11086829549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (231687219735813 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (629075871166439 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (858949320727303 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000)))) (orderedInterval (-1341874970 / 1000000000000) (-1341874532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (363197123558661 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1476376143164581 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (986150842363979 / 4000000000000) 3 (IntervalRat.scale (397 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000)))) (orderedInterval (2836258894 / 1000000000000) (2836303385 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate326_chunkChecks3 :
    compactCertificate326.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate326.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate326_chunkChecks3_0
    compactCertificate326_chunkChecks3_1 compactCertificate326_chunkChecks3_2

theorem compactCertificate326_chunkChecks4_0 :
    compactCertificate326.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (397 / 2) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55430038007 / 1000000000000) (-55430038004 / 1000000000000), orderedInterval (-11464432773 / 1000000000000) (-11464432770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (584856806316697 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40253304695 / 1000000000000) (40253323179 / 1000000000000), orderedInterval (-52422443281 / 1000000000000) (-52422424797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (189130674521401 / 800000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-51890732348 / 1000000000000) (-51890732248 / 1000000000000), orderedInterval (523180778 / 1000000000000) (523180878 / 1000000000000)))) (orderedInterval (-28032154184 / 1000000000000) (-28032154094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (170659757429579 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62264825113 / 1000000000000) (-62264815854 / 1000000000000), orderedInterval (105824613207 / 1000000000000) (105824622466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (458416113736463 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56022888780 / 1000000000000) (56022996410 / 1000000000000), orderedInterval (-49401091213 / 1000000000000) (-49400983583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1244688923428371 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-36515042235 / 1000000000000) (-36515042234 / 1000000000000), orderedInterval (-26634524493 / 1000000000000) (-26634524492 / 1000000000000)))) (orderedInterval (15974207663 / 1000000000000) (15974208195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (916832227473323 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32172475975 / 1000000000000) (-32172475974 / 1000000000000), orderedInterval (-41671991631 / 1000000000000) (-41671991630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1571007648680279 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29923593529 / 1000000000000) (-29923593528 / 1000000000000), orderedInterval (-26896999227 / 1000000000000) (-26896999226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1157197123558661 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40869926716 / 1000000000000) (40869926717 / 1000000000000), orderedInterval (22955547707 / 1000000000000) (22955547708 / 1000000000000)))) (orderedInterval (18683512539 / 1000000000000) (18683512656 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate326_chunkChecks4_1 :
    compactCertificate326.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1775437974134603 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37646122194 / 1000000000000) (-37646120799 / 1000000000000), orderedInterval (4171674383 / 1000000000000) (4171675778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1025049592295987 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26614244396 / 1000000000000) (-26614240242 / 1000000000000), orderedInterval (42193754746 / 1000000000000) (42193758900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1818968489431183 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (138032157 / 1000000000000) (138032158 / 1000000000000), orderedInterval (-37415918152 / 1000000000000) (-37415918151 / 1000000000000)))) (orderedInterval (161632148452 / 1000000000000) (161632157244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1699516313213227 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38699531722 / 1000000000000) (-38699531477 / 1000000000000), orderedInterval (-791362075 / 1000000000000) (-791361830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1212855033931291 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30752264771 / 1000000000000) (30752283333 / 1000000000000), orderedInterval (-34019411851 / 1000000000000) (-34019393289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1375248341209389 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35690721556 / 1000000000000) (-35690624134 / 1000000000000), orderedInterval (24089852943 / 1000000000000) (24089950365 / 1000000000000)))) (orderedInterval (32001618584 / 1000000000000) (32001632947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1146538690053341 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-47096911296 / 1000000000000) (-47096911220 / 1000000000000), orderedInterval (-1618465612 / 1000000000000) (-1618465536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1013001703692161 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21068264566 / 1000000000000) (21068265547 / 1000000000000), orderedInterval (-45538044698 / 1000000000000) (-45538043717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (293607377367939 / 800000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9411360572 / 1000000000000) (-9411360571 / 1000000000000), orderedInterval (-40558632970 / 1000000000000) (-40558632969 / 1000000000000)))) (orderedInterval (-8386812672 / 1000000000000) (-8386812418 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate326_chunkChecks4_2 :
    compactCertificate326.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (812133457509433 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21049236550 / 1000000000000) (21049237294 / 1000000000000), orderedInterval (-51940940706 / 1000000000000) (-51940939962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (688454526062513 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6719252849 / 1000000000000) (-6719252848 / 1000000000000), orderedInterval (-60426332026 / 1000000000000) (-60426332025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (430802876441339 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76498492361 / 1000000000000) (76498492507 / 1000000000000), orderedInterval (-8031454650 / 1000000000000) (-8031454504 / 1000000000000)))) (orderedInterval (-3141211553 / 1000000000000) (-3141211378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (231687219735813 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87369460894 / 1000000000000) (87369486818 / 1000000000000), orderedInterval (-58697549156 / 1000000000000) (-58697523232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (629075871166439 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52623347915 / 1000000000000) (52623347916 / 1000000000000), orderedInterval (35592226417 / 1000000000000) (35592226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (858949320727303 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51631945514 / 1000000000000) (51631949656 / 1000000000000), orderedInterval (-17405468429 / 1000000000000) (-17405464287 / 1000000000000)))) (orderedInterval (-5887910075 / 1000000000000) (-5887909609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (363197123558661 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38451666725 / 1000000000000) (-38451666724 / 1000000000000), orderedInterval (-74171176376 / 1000000000000) (-74171176375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1476376143164581 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30614375915 / 1000000000000) (-30614343542 / 1000000000000), orderedInterval (28105277433 / 1000000000000) (28105309805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (986150842363979 / 4000000000000) 4 (IntervalRat.scale (397 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38616749709 / 1000000000000) (38616825431 / 1000000000000), orderedInterval (-33108397442 / 1000000000000) (-33108321721 / 1000000000000)))) (orderedInterval (12509965294 / 1000000000000) (12510031328 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate326_chunkChecks4 :
    compactCertificate326.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate326.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate326_chunkChecks4_0
    compactCertificate326_chunkChecks4_1 compactCertificate326_chunkChecks4_2

theorem compactCertificate326_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate326.chunkCheck r b = true :=
  compactCertificate326.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate326_chunkChecks0
    · exact compactCertificate326_chunkChecks1
    · exact compactCertificate326_chunkChecks2
    · exact compactCertificate326_chunkChecks3
    · exact compactCertificate326_chunkChecks4)

theorem compactCertificate326_coefficient0 :
    compactCertificate326.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate326_coefficient1 :
    compactCertificate326.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate326_coefficient2 :
    compactCertificate326.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate326_coefficient3 :
    compactCertificate326.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate326_coefficient4 :
    compactCertificate326.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate326_coefficients : ∀ r : Fin 5,
    compactCertificate326.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate326_coefficient0
  · exact compactCertificate326_coefficient1
  · exact compactCertificate326_coefficient2
  · exact compactCertificate326_coefficient3
  · exact compactCertificate326_coefficient4

theorem compactCertificate326_lower : (1 : ℚ) ≤ compactCertificate326.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate326, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate326_proves {t : ℝ} (ht : t ∈ compactCertificate326.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate326.proves compactCertificate326_states compactCertificate326_chunks
    compactCertificate326_coefficients compactCertificate326_lower ht

end Erdos232
