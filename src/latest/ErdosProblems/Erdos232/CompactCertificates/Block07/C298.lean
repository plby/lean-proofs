/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate298 : CompactCertificate where
  left := 171
  right := 172
  center := 343 / 2
  grid := fun i =>
    match i.val with
    | 0 => 55
    | 1 => 40
    | 2 => 65
    | 3 => 12
    | 4 => 32
    | 5 => 86
    | 6 => 63
    | 7 => 108
    | 8 => 80
    | 9 => 122
    | 10 => 71
    | 11 => 125
    | 12 => 117
    | 13 => 83
    | 14 => 95
    | 15 => 79
    | 16 => 70
    | 17 => 101
    | 18 => 56
    | 19 => 47
    | 20 => 30
    | 21 => 16
    | 22 => 43
    | 23 => 59
    | 24 => 25
    | 25 => 102
    | _ => 68
  point := fun i =>
    match i.val with
    | 0 => 343 / 2
    | 1 => 505304495130043 / 4000000000000
    | 2 => 163405091589019 / 800000000000
    | 3 => 147446591431601 / 4000000000000
    | 4 => 396062284663997 / 4000000000000
    | 5 => 1075386147949449 / 4000000000000
    | 6 => 792124569328337 / 4000000000000
    | 7 => 1357318950874901 / 4000000000000
    | 8 => 999794995920959 / 4000000000000
    | 9 => 1533942632564657 / 4000000000000
    | 10 => 885622191832553 / 4000000000000
    | 11 => 1571552120591677 / 4000000000000
    | 12 => 1468347847436113 / 4000000000000
    | 13 => 1047882308912929 / 4000000000000
    | 14 => 1188186853991991 / 4000000000000
    | 15 => 990586324151879 / 4000000000000
    | 16 => 875213058857459 / 4000000000000
    | 17 => 253670857524441 / 800000000000
    | 18 => 701666941878427 / 4000000000000
    | 19 => 594810837378947 / 4000000000000
    | 20 => 372205004079041 / 4000000000000
    | 21 => 200173089091647 / 4000000000000
    | 22 => 543508876095941 / 4000000000000
    | 23 => 742114904305957 / 4000000000000
    | 24 => 313794995920959 / 4000000000000
    | 25 => 1275559237041439 / 4000000000000
    | _ => 852014455745201 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))
    | 1 => (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))
    | 2 => (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000))
    | 3 => (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))
    | 4 => (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))
    | 5 => (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000))
    | 6 => (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))
    | 7 => (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))
    | 8 => (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000))
    | 9 => (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))
    | 10 => (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))
    | 11 => (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000))
    | 12 => (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))
    | 13 => (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))
    | 14 => (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000))
    | 15 => (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))
    | 16 => (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))
    | 17 => (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000))
    | 18 => (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))
    | 19 => (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))
    | 20 => (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000))
    | 21 => (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))
    | 22 => (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))
    | 23 => (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000))
    | 24 => (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))
    | 25 => (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))
    | _ => (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9861817980 / 1000000000000) (9861819355 / 1000000000000)
      | 1 => orderedInterval (-81216861 / 1000000000000) (-81214941 / 1000000000000)
      | 2 => orderedInterval (-1661716516 / 1000000000000) (-1661716362 / 1000000000000)
      | 3 => orderedInterval (-7793389926 / 1000000000000) (-7793383635 / 1000000000000)
      | 4 => orderedInterval (-4142130446 / 1000000000000) (-4142128883 / 1000000000000)
      | 5 => orderedInterval (216850548 / 1000000000000) (216850583 / 1000000000000)
      | 6 => orderedInterval (-92085505 / 1000000000000) (-92085316 / 1000000000000)
      | 7 => orderedInterval (4121711226 / 1000000000000) (4121711248 / 1000000000000)
      | _ => orderedInterval (543437698 / 1000000000000) (543439640 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-23738693973 / 1000000000000) (-23738692596 / 1000000000000)
      | 1 => orderedInterval (-3683517285 / 1000000000000) (-3683515939 / 1000000000000)
      | 2 => orderedInterval (-319798718 / 1000000000000) (-319798492 / 1000000000000)
      | 3 => orderedInterval (-19475535626 / 1000000000000) (-19475527452 / 1000000000000)
      | 4 => orderedInterval (4861692693 / 1000000000000) (4861695088 / 1000000000000)
      | 5 => orderedInterval (-6337476169 / 1000000000000) (-6337476122 / 1000000000000)
      | 6 => orderedInterval (-8981277827 / 1000000000000) (-8981277681 / 1000000000000)
      | 7 => orderedInterval (2257733100 / 1000000000000) (2257733121 / 1000000000000)
      | _ => orderedInterval (-17635859789 / 1000000000000) (-17635856200 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8404443433 / 1000000000000) (-8404442047 / 1000000000000)
      | 1 => orderedInterval (-3741210012 / 1000000000000) (-3741208855 / 1000000000000)
      | 2 => orderedInterval (5285212141 / 1000000000000) (5285212477 / 1000000000000)
      | 3 => orderedInterval (50314767663 / 1000000000000) (50314778384 / 1000000000000)
      | 4 => orderedInterval (9218666545 / 1000000000000) (9218670232 / 1000000000000)
      | 5 => orderedInterval (862452251 / 1000000000000) (862452316 / 1000000000000)
      | 6 => orderedInterval (390271646 / 1000000000000) (390271766 / 1000000000000)
      | 7 => orderedInterval (-5195986963 / 1000000000000) (-5195986943 / 1000000000000)
      | _ => orderedInterval (-6034273124 / 1000000000000) (-6034266455 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (24903328784 / 1000000000000) (24903330173 / 1000000000000)
      | 1 => orderedInterval (11019808746 / 1000000000000) (11019810000 / 1000000000000)
      | 2 => orderedInterval (3863163303 / 1000000000000) (3863163802 / 1000000000000)
      | 3 => orderedInterval (87759521631 / 1000000000000) (87759535744 / 1000000000000)
      | 4 => orderedInterval (-15066644465 / 1000000000000) (-15066638806 / 1000000000000)
      | 5 => orderedInterval (13874438103 / 1000000000000) (13874438195 / 1000000000000)
      | 6 => orderedInterval (10154717652 / 1000000000000) (10154717754 / 1000000000000)
      | 7 => orderedInterval (-3170901692 / 1000000000000) (-3170901672 / 1000000000000)
      | _ => orderedInterval (36317911971 / 1000000000000) (36317924338 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (6644244079 / 1000000000000) (6644245479 / 1000000000000)
      | 1 => orderedInterval (10493361034 / 1000000000000) (10493362684 / 1000000000000)
      | 2 => orderedInterval (-18132701350 / 1000000000000) (-18132700598 / 1000000000000)
      | 3 => orderedInterval (-274958912337 / 1000000000000) (-274958893421 / 1000000000000)
      | 4 => orderedInterval (-19342057898 / 1000000000000) (-19342049170 / 1000000000000)
      | 5 => orderedInterval (-5447187125 / 1000000000000) (-5447186991 / 1000000000000)
      | 6 => orderedInterval (-1024757576 / 1000000000000) (-1024757486 / 1000000000000)
      | 7 => orderedInterval (5675654864 / 1000000000000) (5675654886 / 1000000000000)
      | _ => orderedInterval (25861395075 / 1000000000000) (25861418101 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (973278198 / 1000000000000) (973291689 / 1000000000000)
    | 1 => orderedInterval (-73052733594 / 1000000000000) (-73052716273 / 1000000000000)
    | 2 => orderedInterval (42695456714 / 1000000000000) (42695480875 / 1000000000000)
    | 3 => orderedInterval (169655344033 / 1000000000000) (169655379528 / 1000000000000)
    | _ => orderedInterval (-270230961234 / 1000000000000) (-270230906516 / 1000000000000)

theorem compactCertificate298_stateChecks0 :
    compactCertificate298.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (343 / 2)) (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (505304495130043 / 4000000000000)) (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163405091589019 / 800000000000)) (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks1 :
    compactCertificate298.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (147446591431601 / 4000000000000)) (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (396062284663997 / 4000000000000)) (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1075386147949449 / 4000000000000)) (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks2 :
    compactCertificate298.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (792124569328337 / 4000000000000)) (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1357318950874901 / 4000000000000)) (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (999794995920959 / 4000000000000)) (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks3 :
    compactCertificate298.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1533942632564657 / 4000000000000)) (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (885622191832553 / 4000000000000)) (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1571552120591677 / 4000000000000)) (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks4 :
    compactCertificate298.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1468347847436113 / 4000000000000)) (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1047882308912929 / 4000000000000)) (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1188186853991991 / 4000000000000)) (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks5 :
    compactCertificate298.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (990586324151879 / 4000000000000)) (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875213058857459 / 4000000000000)) (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (253670857524441 / 800000000000)) (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks6 :
    compactCertificate298.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (701666941878427 / 4000000000000)) (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (594810837378947 / 4000000000000)) (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (372205004079041 / 4000000000000)) (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks7 :
    compactCertificate298.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (200173089091647 / 4000000000000)) (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543508876095941 / 4000000000000)) (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742114904305957 / 4000000000000)) (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_stateChecks8 :
    compactCertificate298.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (313794995920959 / 4000000000000)) (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1275559237041439 / 4000000000000)) (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (852014455745201 / 4000000000000)) (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_states : ∀ j,
    BesselStateValid (compactCertificate298.point j) (compactCertificate298.state j) :=
  compactCertificate298.statesValid_of_checks3 compactCertificate298_stateChecks0
    compactCertificate298_stateChecks1 compactCertificate298_stateChecks2
    compactCertificate298_stateChecks3 compactCertificate298_stateChecks4
    compactCertificate298_stateChecks5 compactCertificate298_stateChecks6
    compactCertificate298_stateChecks7 compactCertificate298_stateChecks8

theorem compactCertificate298_chunkChecks0_0 :
    compactCertificate298.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (343 / 2) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (505304495130043 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (163405091589019 / 800000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000)))) (orderedInterval (9861817980 / 1000000000000) (9861819355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (147446591431601 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (396062284663997 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1075386147949449 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000)))) (orderedInterval (-81216861 / 1000000000000) (-81214941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (792124569328337 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1357318950874901 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (999794995920959 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000)))) (orderedInterval (-1661716516 / 1000000000000) (-1661716362 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks0_1 :
    compactCertificate298.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1533942632564657 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (885622191832553 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1571552120591677 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000)))) (orderedInterval (-7793389926 / 1000000000000) (-7793383635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1468347847436113 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1047882308912929 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1188186853991991 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000)))) (orderedInterval (-4142130446 / 1000000000000) (-4142128883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (990586324151879 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (875213058857459 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (253670857524441 / 800000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000)))) (orderedInterval (216850548 / 1000000000000) (216850583 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks0_2 :
    compactCertificate298.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (701666941878427 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (594810837378947 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (372205004079041 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000)))) (orderedInterval (-92085505 / 1000000000000) (-92085316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (200173089091647 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (543508876095941 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (742114904305957 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000)))) (orderedInterval (4121711226 / 1000000000000) (4121711248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (313794995920959 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1275559237041439 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (852014455745201 / 4000000000000) 0 (IntervalRat.scale (343 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000)))) (orderedInterval (543437698 / 1000000000000) (543439640 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks0 :
    compactCertificate298.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate298.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate298_chunkChecks0_0
    compactCertificate298_chunkChecks0_1 compactCertificate298_chunkChecks0_2

theorem compactCertificate298_chunkChecks1_0 :
    compactCertificate298.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (343 / 2) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (505304495130043 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (163405091589019 / 800000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000)))) (orderedInterval (-23738693973 / 1000000000000) (-23738692596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (147446591431601 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (396062284663997 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1075386147949449 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000)))) (orderedInterval (-3683517285 / 1000000000000) (-3683515939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (792124569328337 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1357318950874901 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (999794995920959 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000)))) (orderedInterval (-319798718 / 1000000000000) (-319798492 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks1_1 :
    compactCertificate298.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1533942632564657 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (885622191832553 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1571552120591677 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000)))) (orderedInterval (-19475535626 / 1000000000000) (-19475527452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1468347847436113 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1047882308912929 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1188186853991991 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000)))) (orderedInterval (4861692693 / 1000000000000) (4861695088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (990586324151879 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (875213058857459 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (253670857524441 / 800000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000)))) (orderedInterval (-6337476169 / 1000000000000) (-6337476122 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks1_2 :
    compactCertificate298.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (701666941878427 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (594810837378947 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (372205004079041 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000)))) (orderedInterval (-8981277827 / 1000000000000) (-8981277681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (200173089091647 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (543508876095941 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (742114904305957 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000)))) (orderedInterval (2257733100 / 1000000000000) (2257733121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (313794995920959 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1275559237041439 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (852014455745201 / 4000000000000) 1 (IntervalRat.scale (343 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000)))) (orderedInterval (-17635859789 / 1000000000000) (-17635856200 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks1 :
    compactCertificate298.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate298.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate298_chunkChecks1_0
    compactCertificate298_chunkChecks1_1 compactCertificate298_chunkChecks1_2

theorem compactCertificate298_chunkChecks2_0 :
    compactCertificate298.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (343 / 2) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (505304495130043 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (163405091589019 / 800000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000)))) (orderedInterval (-8404443433 / 1000000000000) (-8404442047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (147446591431601 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (396062284663997 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1075386147949449 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000)))) (orderedInterval (-3741210012 / 1000000000000) (-3741208855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (792124569328337 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1357318950874901 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (999794995920959 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000)))) (orderedInterval (5285212141 / 1000000000000) (5285212477 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks2_1 :
    compactCertificate298.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1533942632564657 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (885622191832553 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1571552120591677 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000)))) (orderedInterval (50314767663 / 1000000000000) (50314778384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1468347847436113 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1047882308912929 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1188186853991991 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000)))) (orderedInterval (9218666545 / 1000000000000) (9218670232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (990586324151879 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (875213058857459 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (253670857524441 / 800000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000)))) (orderedInterval (862452251 / 1000000000000) (862452316 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks2_2 :
    compactCertificate298.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (701666941878427 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (594810837378947 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (372205004079041 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000)))) (orderedInterval (390271646 / 1000000000000) (390271766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (200173089091647 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (543508876095941 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (742114904305957 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000)))) (orderedInterval (-5195986963 / 1000000000000) (-5195986943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (313794995920959 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1275559237041439 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (852014455745201 / 4000000000000) 2 (IntervalRat.scale (343 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000)))) (orderedInterval (-6034273124 / 1000000000000) (-6034266455 / 1000000000000))) = true
  rfl'

theorem compactCertificate298_chunkChecks2 :
    compactCertificate298.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate298.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate298_chunkChecks2_0
    compactCertificate298_chunkChecks2_1 compactCertificate298_chunkChecks2_2

theorem compactCertificate298_chunkChecks3_0 :
    compactCertificate298.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (343 / 2) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (505304495130043 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (163405091589019 / 800000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000)))) (orderedInterval (24903328784 / 1000000000000) (24903330173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (147446591431601 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (396062284663997 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1075386147949449 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000)))) (orderedInterval (11019808746 / 1000000000000) (11019810000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (792124569328337 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1357318950874901 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (999794995920959 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000)))) (orderedInterval (3863163303 / 1000000000000) (3863163802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate298_chunkChecks3_1 :
    compactCertificate298.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1533942632564657 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (885622191832553 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1571552120591677 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000)))) (orderedInterval (87759521631 / 1000000000000) (87759535744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1468347847436113 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1047882308912929 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1188186853991991 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000)))) (orderedInterval (-15066644465 / 1000000000000) (-15066638806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (990586324151879 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (875213058857459 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (253670857524441 / 800000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000)))) (orderedInterval (13874438103 / 1000000000000) (13874438195 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate298_chunkChecks3_2 :
    compactCertificate298.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (701666941878427 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (594810837378947 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (372205004079041 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000)))) (orderedInterval (10154717652 / 1000000000000) (10154717754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (200173089091647 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (543508876095941 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (742114904305957 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000)))) (orderedInterval (-3170901692 / 1000000000000) (-3170901672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (313794995920959 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1275559237041439 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (852014455745201 / 4000000000000) 3 (IntervalRat.scale (343 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000)))) (orderedInterval (36317911971 / 1000000000000) (36317924338 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate298_chunkChecks3 :
    compactCertificate298.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate298.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate298_chunkChecks3_0
    compactCertificate298_chunkChecks3_1 compactCertificate298_chunkChecks3_2

theorem compactCertificate298_chunkChecks4_0 :
    compactCertificate298.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (343 / 2) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29366131553 / 1000000000000) (29366134990 / 1000000000000), orderedInterval (-53468266289 / 1000000000000) (-53468262851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (505304495130043 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70444315252 / 1000000000000) (70444315258 / 1000000000000), orderedInterval (8499249749 / 1000000000000) (8499249755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (163405091589019 / 800000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41483394796 / 1000000000000) (-41483394795 / 1000000000000), orderedInterval (-37260135930 / 1000000000000) (-37260135929 / 1000000000000)))) (orderedInterval (6644244079 / 1000000000000) (6644245479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (147446591431601 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-7283756072 / 1000000000000) (-7283756048 / 1000000000000), orderedInterval (131320130226 / 1000000000000) (131320130251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (396062284663997 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53547149731 / 1000000000000) (-53547103975 / 1000000000000), orderedInterval (59954580630 / 1000000000000) (59954626386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1075386147949449 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25247837705 / 1000000000000) (-25247834503 / 1000000000000), orderedInterval (41646423098 / 1000000000000) (41646426300 / 1000000000000)))) (orderedInterval (10493361034 / 1000000000000) (10493362684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (792124569328337 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44257075290 / 1000000000000) (-44257075289 / 1000000000000), orderedInterval (-35329121322 / 1000000000000) (-35329121321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1357318950874901 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31750356066 / 1000000000000) (31750356067 / 1000000000000), orderedInterval (29415468625 / 1000000000000) (29415468626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (999794995920959 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28236003545 / 1000000000000) (-28235997625 / 1000000000000), orderedInterval (41886271188 / 1000000000000) (41886277108 / 1000000000000)))) (orderedInterval (-18132701350 / 1000000000000) (-18132700598 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate298_chunkChecks4_1 :
    compactCertificate298.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1533942632564657 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34206140198 / 1000000000000) (34206140199 / 1000000000000), orderedInterval (22091953660 / 1000000000000) (22091953661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (885622191832553 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40731402566 / 1000000000000) (40731486540 / 1000000000000), orderedInterval (-34967576424 / 1000000000000) (-34967492449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1571552120591677 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33296077060 / 1000000000000) (-33296077059 / 1000000000000), orderedInterval (-22579078036 / 1000000000000) (-22579078035 / 1000000000000)))) (orderedInterval (-274958912337 / 1000000000000) (-274958893421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1468347847436113 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12532463643 / 1000000000000) (-12532463642 / 1000000000000), orderedInterval (-39696737512 / 1000000000000) (-39696737511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1047882308912929 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44756805019 / 1000000000000) (-44756789041 / 1000000000000), orderedInterval (20748076416 / 1000000000000) (20748092395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1188186853991991 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26883954157 / 1000000000000) (26883960203 / 1000000000000), orderedInterval (-37733683604 / 1000000000000) (-37733677558 / 1000000000000)))) (orderedInterval (-19342057898 / 1000000000000) (-19342049170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (990586324151879 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12330250817 / 1000000000000) (-12330250816 / 1000000000000), orderedInterval (-49154858798 / 1000000000000) (-49154858797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (875213058857459 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17141474418 / 1000000000000) (-17141474109 / 1000000000000), orderedInterval (51183371401 / 1000000000000) (51183371710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (253670857524441 / 800000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24281932187 / 1000000000000) (-24281932186 / 1000000000000), orderedInterval (-37619274862 / 1000000000000) (-37619274861 / 1000000000000)))) (orderedInterval (-5447187125 / 1000000000000) (-5447186991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate298_chunkChecks4_2 :
    compactCertificate298.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (701666941878427 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16198170100 / 1000000000000) (16198170101 / 1000000000000), orderedInterval (57978107713 / 1000000000000) (57978107714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (594810837378947 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63203993988 / 1000000000000) (-63203992540 / 1000000000000), orderedInterval (17135638811 / 1000000000000) (17135640258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (372205004079041 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33157878087 / 1000000000000) (-33157876137 / 1000000000000), orderedInterval (75955639194 / 1000000000000) (75955641143 / 1000000000000)))) (orderedInterval (-1024757576 / 1000000000000) (-1024757486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (200173089091647 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59976514321 / 1000000000000) (59976514322 / 1000000000000), orderedInterval (94922953080 / 1000000000000) (94922953081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (543508876095941 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-68448509936 / 1000000000000) (-68448509891 / 1000000000000), orderedInterval (417303022 / 1000000000000) (417303067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (742114904305957 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47969166200 / 1000000000000) (-47969166199 / 1000000000000), orderedInterval (-33491193779 / 1000000000000) (-33491193778 / 1000000000000)))) (orderedInterval (5675654864 / 1000000000000) (5675654886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (313794995920959 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57531131272 / 1000000000000) (-57531131271 / 1000000000000), orderedInterval (-68953631617 / 1000000000000) (-68953631616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1275559237041439 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31027844448 / 1000000000000) (-31027821181 / 1000000000000), orderedInterval (32198855680 / 1000000000000) (32198878947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (852014455745201 / 4000000000000) 4 (IntervalRat.scale (343 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8716600767 / 1000000000000) (8716600768 / 1000000000000), orderedInterval (53949930827 / 1000000000000) (53949930828 / 1000000000000)))) (orderedInterval (25861395075 / 1000000000000) (25861418101 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate298_chunkChecks4 :
    compactCertificate298.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate298.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate298_chunkChecks4_0
    compactCertificate298_chunkChecks4_1 compactCertificate298_chunkChecks4_2

theorem compactCertificate298_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate298.chunkCheck r b = true :=
  compactCertificate298.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate298_chunkChecks0
    · exact compactCertificate298_chunkChecks1
    · exact compactCertificate298_chunkChecks2
    · exact compactCertificate298_chunkChecks3
    · exact compactCertificate298_chunkChecks4)

theorem compactCertificate298_coefficient0 :
    compactCertificate298.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate298_coefficient1 :
    compactCertificate298.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate298_coefficient2 :
    compactCertificate298.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate298_coefficient3 :
    compactCertificate298.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate298_coefficient4 :
    compactCertificate298.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate298_coefficients : ∀ r : Fin 5,
    compactCertificate298.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate298_coefficient0
  · exact compactCertificate298_coefficient1
  · exact compactCertificate298_coefficient2
  · exact compactCertificate298_coefficient3
  · exact compactCertificate298_coefficient4

theorem compactCertificate298_lower : (1 : ℚ) ≤ compactCertificate298.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate298, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate298_proves {t : ℝ} (ht : t ∈ compactCertificate298.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate298.proves compactCertificate298_states compactCertificate298_chunks
    compactCertificate298_coefficients compactCertificate298_lower ht

end Erdos232
