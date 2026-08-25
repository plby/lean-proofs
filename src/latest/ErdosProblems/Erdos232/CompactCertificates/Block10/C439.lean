/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate439 : CompactCertificate where
  left := 310
  right := 311
  center := 621 / 2
  grid := fun i =>
    match i.val with
    | 0 => 99
    | 1 => 73
    | 2 => 118
    | 3 => 21
    | 4 => 57
    | 5 => 155
    | 6 => 114
    | 7 => 196
    | 8 => 144
    | 9 => 221
    | 10 => 128
    | 11 => 227
    | 12 => 212
    | 13 => 151
    | 14 => 171
    | 15 => 143
    | 16 => 126
    | 17 => 183
    | 18 => 101
    | 19 => 86
    | 20 => 54
    | 21 => 29
    | 22 => 78
    | 23 => 107
    | 24 => 45
    | 25 => 184
    | _ => 123
  point := fun i =>
    match i.val with
    | 0 => 621 / 2
    | 1 => 914851578646521 / 4000000000000
    | 2 => 295844203722393 / 800000000000
    | 3 => 266951408976747 / 4000000000000
    | 4 => 717069034333359 / 4000000000000
    | 5 => 1946981918007603 / 4000000000000
    | 6 => 1434138068667339 / 4000000000000
    | 7 => 2457420024761847 / 4000000000000
    | 8 => 1810124467833573 / 4000000000000
    | 9 => 2777196428054379 / 4000000000000
    | 10 => 1603415105329491 / 4000000000000
    | 11 => 2845288241654319 / 4000000000000
    | 12 => 2658437356436811 / 4000000000000
    | 13 => 1897186337711163 / 4000000000000
    | 14 => 2151207103000077 / 4000000000000
    | 15 => 1793452207866813 / 4000000000000
    | 16 => 1584569415599073 / 4000000000000
    | 17 => 459269978200227 / 800000000000
    | 18 => 1270364929756569 / 4000000000000
    | 19 => 1076902419861009 / 4000000000000
    | 20 => 673875532166427 / 4000000000000
    | 21 => 362412502407909 / 4000000000000
    | 22 => 984020443310727 / 4000000000000
    | 23 => 1343595788845479 / 4000000000000
    | 24 => 568124467833573 / 4000000000000
    | 25 => 2309394420416133 / 4000000000000
    | _ => 1542568446115947 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))
    | 1 => (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))
    | 2 => (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000))
    | 3 => (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))
    | 4 => (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
    | 5 => (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000))
    | 6 => (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))
    | 7 => (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))
    | 8 => (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000))
    | 9 => (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))
    | 10 => (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))
    | 11 => (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000))
    | 12 => (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))
    | 13 => (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))
    | 14 => (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000))
    | 15 => (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))
    | 16 => (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))
    | 17 => (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000))
    | 18 => (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))
    | 19 => (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))
    | 20 => (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000))
    | 21 => (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))
    | 22 => (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))
    | 23 => (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000))
    | 24 => (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))
    | 25 => (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))
    | _ => (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-5105593325 / 1000000000000) (-5105593302 / 1000000000000)
      | 1 => orderedInterval (667930591 / 1000000000000) (667930629 / 1000000000000)
      | 2 => orderedInterval (1295352549 / 1000000000000) (1295352596 / 1000000000000)
      | 3 => orderedInterval (6109561300 / 1000000000000) (6109567618 / 1000000000000)
      | 4 => orderedInterval (-1738296453 / 1000000000000) (-1738296401 / 1000000000000)
      | 5 => orderedInterval (-1954233388 / 1000000000000) (-1954233357 / 1000000000000)
      | 6 => orderedInterval (5988546772 / 1000000000000) (5988546885 / 1000000000000)
      | 7 => orderedInterval (989617889 / 1000000000000) (989617948 / 1000000000000)
      | _ => orderedInterval (-532296365 / 1000000000000) (-532296278 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14779515135 / 1000000000000) (-14779515109 / 1000000000000)
      | 1 => orderedInterval (2668479864 / 1000000000000) (2668479907 / 1000000000000)
      | 2 => orderedInterval (-817005840 / 1000000000000) (-817005753 / 1000000000000)
      | 3 => orderedInterval (6830321558 / 1000000000000) (6830335949 / 1000000000000)
      | 4 => orderedInterval (-4953010789 / 1000000000000) (-4953010698 / 1000000000000)
      | 5 => orderedInterval (-3559341195 / 1000000000000) (-3559341152 / 1000000000000)
      | 6 => orderedInterval (2121107862 / 1000000000000) (2121107953 / 1000000000000)
      | 7 => orderedInterval (3699211924 / 1000000000000) (3699211975 / 1000000000000)
      | _ => orderedInterval (4435319822 / 1000000000000) (4435319944 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5236600123 / 1000000000000) (5236600153 / 1000000000000)
      | 1 => orderedInterval (-2936952113 / 1000000000000) (-2936952054 / 1000000000000)
      | 2 => orderedInterval (-3770246612 / 1000000000000) (-3770246446 / 1000000000000)
      | 3 => orderedInterval (-36065529103 / 1000000000000) (-36065496197 / 1000000000000)
      | 4 => orderedInterval (3225103774 / 1000000000000) (3225103939 / 1000000000000)
      | 5 => orderedInterval (3113387559 / 1000000000000) (3113387623 / 1000000000000)
      | 6 => orderedInterval (-6713253912 / 1000000000000) (-6713253832 / 1000000000000)
      | 7 => orderedInterval (-1320963674 / 1000000000000) (-1320963627 / 1000000000000)
      | _ => orderedInterval (690464412 / 1000000000000) (690464591 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (13393765376 / 1000000000000) (13393765410 / 1000000000000)
      | 1 => orderedInterval (-8017176458 / 1000000000000) (-8017176369 / 1000000000000)
      | 2 => orderedInterval (4628747242 / 1000000000000) (4628747563 / 1000000000000)
      | 3 => orderedInterval (-21549600519 / 1000000000000) (-21549525281 / 1000000000000)
      | 4 => orderedInterval (13692206813 / 1000000000000) (13692207122 / 1000000000000)
      | 5 => orderedInterval (8890543385 / 1000000000000) (8890543484 / 1000000000000)
      | 6 => orderedInterval (-2135303555 / 1000000000000) (-2135303482 / 1000000000000)
      | 7 => orderedInterval (-3767361000 / 1000000000000) (-3767360954 / 1000000000000)
      | _ => orderedInterval (2717973948 / 1000000000000) (2717974224 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-5425199751 / 1000000000000) (-5425199712 / 1000000000000)
      | 1 => orderedInterval (8410259239 / 1000000000000) (8410259375 / 1000000000000)
      | 2 => orderedInterval (11982831599 / 1000000000000) (11982832221 / 1000000000000)
      | 3 => orderedInterval (192764442143 / 1000000000000) (192764614540 / 1000000000000)
      | 4 => orderedInterval (-3876269794 / 1000000000000) (-3876269202 / 1000000000000)
      | 5 => orderedInterval (-4862556146 / 1000000000000) (-4862555989 / 1000000000000)
      | 6 => orderedInterval (7098418257 / 1000000000000) (7098418327 / 1000000000000)
      | 7 => orderedInterval (1903633037 / 1000000000000) (1903633082 / 1000000000000)
      | _ => orderedInterval (-2436220062 / 1000000000000) (-2436219619 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5720589570 / 1000000000000) (5720596338 / 1000000000000)
    | 1 => orderedInterval (-4354431929 / 1000000000000) (-4354416984 / 1000000000000)
    | 2 => orderedInterval (-38541389546 / 1000000000000) (-38541355850 / 1000000000000)
    | 3 => orderedInterval (7853795232 / 1000000000000) (7853871717 / 1000000000000)
    | _ => orderedInterval (205559338522 / 1000000000000) (205559513023 / 1000000000000)

theorem compactCertificate439_stateChecks0 :
    compactCertificate439.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (621 / 2)) (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (914851578646521 / 4000000000000)) (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (295844203722393 / 800000000000)) (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks1 :
    compactCertificate439.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (266951408976747 / 4000000000000)) (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717069034333359 / 4000000000000)) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1946981918007603 / 4000000000000)) (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks2 :
    compactCertificate439.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1434138068667339 / 4000000000000)) (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2457420024761847 / 4000000000000)) (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1810124467833573 / 4000000000000)) (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks3 :
    compactCertificate439.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2777196428054379 / 4000000000000)) (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1603415105329491 / 4000000000000)) (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2845288241654319 / 4000000000000)) (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks4 :
    compactCertificate439.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2658437356436811 / 4000000000000)) (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1897186337711163 / 4000000000000)) (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2151207103000077 / 4000000000000)) (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks5 :
    compactCertificate439.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1793452207866813 / 4000000000000)) (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1584569415599073 / 4000000000000)) (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (459269978200227 / 800000000000)) (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks6 :
    compactCertificate439.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1270364929756569 / 4000000000000)) (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1076902419861009 / 4000000000000)) (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (673875532166427 / 4000000000000)) (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks7 :
    compactCertificate439.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (362412502407909 / 4000000000000)) (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (984020443310727 / 4000000000000)) (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1343595788845479 / 4000000000000)) (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_stateChecks8 :
    compactCertificate439.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (568124467833573 / 4000000000000)) (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2309394420416133 / 4000000000000)) (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1542568446115947 / 4000000000000)) (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_states : ∀ j,
    BesselStateValid (compactCertificate439.point j) (compactCertificate439.state j) :=
  compactCertificate439.statesValid_of_checks3 compactCertificate439_stateChecks0
    compactCertificate439_stateChecks1 compactCertificate439_stateChecks2
    compactCertificate439_stateChecks3 compactCertificate439_stateChecks4
    compactCertificate439_stateChecks5 compactCertificate439_stateChecks6
    compactCertificate439_stateChecks7 compactCertificate439_stateChecks8

theorem compactCertificate439_chunkChecks0_0 :
    compactCertificate439.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (621 / 2) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (914851578646521 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (295844203722393 / 800000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000)))) (orderedInterval (-5105593325 / 1000000000000) (-5105593302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (266951408976747 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1946981918007603 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000)))) (orderedInterval (667930591 / 1000000000000) (667930629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1434138068667339 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2457420024761847 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1810124467833573 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000)))) (orderedInterval (1295352549 / 1000000000000) (1295352596 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks0_1 :
    compactCertificate439.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2777196428054379 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1603415105329491 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2845288241654319 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000)))) (orderedInterval (6109561300 / 1000000000000) (6109567618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2658437356436811 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1897186337711163 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2151207103000077 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000)))) (orderedInterval (-1738296453 / 1000000000000) (-1738296401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1793452207866813 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1584569415599073 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (459269978200227 / 800000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000)))) (orderedInterval (-1954233388 / 1000000000000) (-1954233357 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks0_2 :
    compactCertificate439.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1270364929756569 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1076902419861009 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (673875532166427 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000)))) (orderedInterval (5988546772 / 1000000000000) (5988546885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (362412502407909 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (984020443310727 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1343595788845479 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000)))) (orderedInterval (989617889 / 1000000000000) (989617948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (568124467833573 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2309394420416133 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1542568446115947 / 4000000000000) 0 (IntervalRat.scale (621 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000)))) (orderedInterval (-532296365 / 1000000000000) (-532296278 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks0 :
    compactCertificate439.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate439.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate439_chunkChecks0_0
    compactCertificate439_chunkChecks0_1 compactCertificate439_chunkChecks0_2

theorem compactCertificate439_chunkChecks1_0 :
    compactCertificate439.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (621 / 2) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (914851578646521 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (295844203722393 / 800000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000)))) (orderedInterval (-14779515135 / 1000000000000) (-14779515109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (266951408976747 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1946981918007603 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000)))) (orderedInterval (2668479864 / 1000000000000) (2668479907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1434138068667339 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2457420024761847 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1810124467833573 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000)))) (orderedInterval (-817005840 / 1000000000000) (-817005753 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks1_1 :
    compactCertificate439.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2777196428054379 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1603415105329491 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2845288241654319 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000)))) (orderedInterval (6830321558 / 1000000000000) (6830335949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2658437356436811 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1897186337711163 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2151207103000077 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000)))) (orderedInterval (-4953010789 / 1000000000000) (-4953010698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1793452207866813 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1584569415599073 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (459269978200227 / 800000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000)))) (orderedInterval (-3559341195 / 1000000000000) (-3559341152 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks1_2 :
    compactCertificate439.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1270364929756569 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1076902419861009 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (673875532166427 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000)))) (orderedInterval (2121107862 / 1000000000000) (2121107953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (362412502407909 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (984020443310727 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1343595788845479 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000)))) (orderedInterval (3699211924 / 1000000000000) (3699211975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (568124467833573 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2309394420416133 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1542568446115947 / 4000000000000) 1 (IntervalRat.scale (621 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000)))) (orderedInterval (4435319822 / 1000000000000) (4435319944 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks1 :
    compactCertificate439.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate439.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate439_chunkChecks1_0
    compactCertificate439_chunkChecks1_1 compactCertificate439_chunkChecks1_2

theorem compactCertificate439_chunkChecks2_0 :
    compactCertificate439.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (621 / 2) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (914851578646521 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (295844203722393 / 800000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000)))) (orderedInterval (5236600123 / 1000000000000) (5236600153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (266951408976747 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1946981918007603 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000)))) (orderedInterval (-2936952113 / 1000000000000) (-2936952054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1434138068667339 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2457420024761847 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1810124467833573 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000)))) (orderedInterval (-3770246612 / 1000000000000) (-3770246446 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks2_1 :
    compactCertificate439.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2777196428054379 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1603415105329491 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2845288241654319 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000)))) (orderedInterval (-36065529103 / 1000000000000) (-36065496197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2658437356436811 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1897186337711163 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2151207103000077 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000)))) (orderedInterval (3225103774 / 1000000000000) (3225103939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1793452207866813 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1584569415599073 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (459269978200227 / 800000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000)))) (orderedInterval (3113387559 / 1000000000000) (3113387623 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks2_2 :
    compactCertificate439.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1270364929756569 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1076902419861009 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (673875532166427 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000)))) (orderedInterval (-6713253912 / 1000000000000) (-6713253832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (362412502407909 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (984020443310727 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1343595788845479 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000)))) (orderedInterval (-1320963674 / 1000000000000) (-1320963627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (568124467833573 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2309394420416133 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1542568446115947 / 4000000000000) 2 (IntervalRat.scale (621 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000)))) (orderedInterval (690464412 / 1000000000000) (690464591 / 1000000000000))) = true
  rfl'

theorem compactCertificate439_chunkChecks2 :
    compactCertificate439.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate439.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate439_chunkChecks2_0
    compactCertificate439_chunkChecks2_1 compactCertificate439_chunkChecks2_2

theorem compactCertificate439_chunkChecks3_0 :
    compactCertificate439.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (621 / 2) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (914851578646521 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (295844203722393 / 800000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000)))) (orderedInterval (13393765376 / 1000000000000) (13393765410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (266951408976747 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1946981918007603 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000)))) (orderedInterval (-8017176458 / 1000000000000) (-8017176369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1434138068667339 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2457420024761847 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1810124467833573 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000)))) (orderedInterval (4628747242 / 1000000000000) (4628747563 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate439_chunkChecks3_1 :
    compactCertificate439.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2777196428054379 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1603415105329491 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2845288241654319 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000)))) (orderedInterval (-21549600519 / 1000000000000) (-21549525281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2658437356436811 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1897186337711163 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2151207103000077 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000)))) (orderedInterval (13692206813 / 1000000000000) (13692207122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1793452207866813 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1584569415599073 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (459269978200227 / 800000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000)))) (orderedInterval (8890543385 / 1000000000000) (8890543484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate439_chunkChecks3_2 :
    compactCertificate439.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1270364929756569 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1076902419861009 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (673875532166427 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000)))) (orderedInterval (-2135303555 / 1000000000000) (-2135303482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (362412502407909 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (984020443310727 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1343595788845479 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000)))) (orderedInterval (-3767361000 / 1000000000000) (-3767360954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (568124467833573 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2309394420416133 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1542568446115947 / 4000000000000) 3 (IntervalRat.scale (621 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000)))) (orderedInterval (2717973948 / 1000000000000) (2717974224 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate439_chunkChecks3 :
    compactCertificate439.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate439.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate439_chunkChecks3_0
    compactCertificate439_chunkChecks3_1 compactCertificate439_chunkChecks3_2

theorem compactCertificate439_chunkChecks4_0 :
    compactCertificate439.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (621 / 2) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11960798664 / 1000000000000) (-11960798663 / 1000000000000), orderedInterval (-43652776413 / 1000000000000) (-43652776412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (914851578646521 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8482634783 / 1000000000000) (-8482634782 / 1000000000000), orderedInterval (-52053905122 / 1000000000000) (-52053905121 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (295844203722393 / 800000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4868851142 / 1000000000000) (-4868851137 / 1000000000000), orderedInterval (41210901810 / 1000000000000) (41210901815 / 1000000000000)))) (orderedInterval (-5425199751 / 1000000000000) (-5425199712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (266951408976747 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97641473770 / 1000000000000) (-97641473752 / 1000000000000), orderedInterval (-1501479098 / 1000000000000) (-1501479080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (717069034333359 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49530162378 / 1000000000000) (-49530162377 / 1000000000000), orderedInterval (-32997795604 / 1000000000000) (-32997795603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1946981918007603 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19932897901 / 1000000000000) (-19932897900 / 1000000000000), orderedInterval (-30155522468 / 1000000000000) (-30155522467 / 1000000000000)))) (orderedInterval (8410259239 / 1000000000000) (8410259375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1434138068667339 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38928974764 / 1000000000000) (38928974765 / 1000000000000), orderedInterval (16074880732 / 1000000000000) (16074880733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2457420024761847 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18492657925 / 1000000000000) (-18492656997 / 1000000000000), orderedInterval (26363913649 / 1000000000000) (26363914578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1810124467833573 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29996864352 / 1000000000000) (29996864353 / 1000000000000), orderedInterval (22483198964 / 1000000000000) (22483198965 / 1000000000000)))) (orderedInterval (11982831599 / 1000000000000) (11982832221 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate439_chunkChecks4_1 :
    compactCertificate439.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2777196428054379 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21560031839 / 1000000000000) (-21560031838 / 1000000000000), orderedInterval (-21246867460 / 1000000000000) (-21246867459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1603415105329491 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18579092330 / 1000000000000) (-18579091590 / 1000000000000), orderedInterval (35279061979 / 1000000000000) (35279062719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2845288241654319 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25712348765 / 1000000000000) (25712391954 / 1000000000000), orderedInterval (-15310411226 / 1000000000000) (-15310368037 / 1000000000000)))) (orderedInterval (192764442143 / 1000000000000) (192764614540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2658437356436811 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18060711890 / 1000000000000) (-18060711109 / 1000000000000), orderedInterval (25147159662 / 1000000000000) (25147160443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1897186337711163 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23636335805 / 1000000000000) (-23636335804 / 1000000000000), orderedInterval (-27967288768 / 1000000000000) (-27967288767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2151207103000077 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33745496713 / 1000000000000) (-33745496666 / 1000000000000), orderedInterval (-6675731248 / 1000000000000) (-6675731201 / 1000000000000)))) (orderedInterval (-3876269794 / 1000000000000) (-3876269202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1793452207866813 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3746027773 / 1000000000000) (3746027776 / 1000000000000), orderedInterval (-37498760716 / 1000000000000) (-37498760714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1584569415599073 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35482872334 / 1000000000000) (35482872335 / 1000000000000), orderedInterval (18610321965 / 1000000000000) (18610321966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (459269978200227 / 800000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1291816653 / 1000000000000) (1291816654 / 1000000000000), orderedInterval (-33276586309 / 1000000000000) (-33276586308 / 1000000000000)))) (orderedInterval (-4862556146 / 1000000000000) (-4862555989 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate439_chunkChecks4_2 :
    compactCertificate439.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1270364929756569 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39388993367 / 1000000000000) (-39388993366 / 1000000000000), orderedInterval (-21222524528 / 1000000000000) (-21222524527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1076902419861009 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8055726701 / 1000000000000) (-8055726678 / 1000000000000), orderedInterval (47970588316 / 1000000000000) (47970588339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (673875532166427 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23511071408 / 1000000000000) (-23511070409 / 1000000000000), orderedInterval (56868527936 / 1000000000000) (56868528934 / 1000000000000)))) (orderedInterval (7098418257 / 1000000000000) (7098418327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (362412502407909 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23242169199 / 1000000000000) (-23242169198 / 1000000000000), orderedInterval (-80409669211 / 1000000000000) (-80409669210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (984020443310727 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50093907413 / 1000000000000) (50093908342 / 1000000000000), orderedInterval (-8957708899 / 1000000000000) (-8957707969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1343595788845479 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22141794624 / 1000000000000) (-22141794623 / 1000000000000), orderedInterval (-37450552839 / 1000000000000) (-37450552838 / 1000000000000)))) (orderedInterval (1903633037 / 1000000000000) (1903633082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (568124467833573 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66411688826 / 1000000000000) (-66411688820 / 1000000000000), orderedInterval (-8234759370 / 1000000000000) (-8234759364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2309394420416133 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2678117673 / 1000000000000) (2678117674 / 1000000000000), orderedInterval (33095853781 / 1000000000000) (33095853782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1542568446115947 / 4000000000000) 4 (IntervalRat.scale (621 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-458670000 / 1000000000000) (-458669999 / 1000000000000), orderedInterval (-40626928142 / 1000000000000) (-40626928141 / 1000000000000)))) (orderedInterval (-2436220062 / 1000000000000) (-2436219619 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate439_chunkChecks4 :
    compactCertificate439.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate439.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate439_chunkChecks4_0
    compactCertificate439_chunkChecks4_1 compactCertificate439_chunkChecks4_2

theorem compactCertificate439_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate439.chunkCheck r b = true :=
  compactCertificate439.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate439_chunkChecks0
    · exact compactCertificate439_chunkChecks1
    · exact compactCertificate439_chunkChecks2
    · exact compactCertificate439_chunkChecks3
    · exact compactCertificate439_chunkChecks4)

theorem compactCertificate439_coefficient0 :
    compactCertificate439.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate439_coefficient1 :
    compactCertificate439.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate439_coefficient2 :
    compactCertificate439.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate439_coefficient3 :
    compactCertificate439.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate439_coefficient4 :
    compactCertificate439.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate439_coefficients : ∀ r : Fin 5,
    compactCertificate439.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate439_coefficient0
  · exact compactCertificate439_coefficient1
  · exact compactCertificate439_coefficient2
  · exact compactCertificate439_coefficient3
  · exact compactCertificate439_coefficient4

theorem compactCertificate439_lower : (1 : ℚ) ≤ compactCertificate439.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate439, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate439_proves {t : ℝ} (ht : t ∈ compactCertificate439.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate439.proves compactCertificate439_states compactCertificate439_chunks
    compactCertificate439_coefficients compactCertificate439_lower ht

end Erdos232
