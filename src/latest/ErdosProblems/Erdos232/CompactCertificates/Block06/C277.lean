/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate277 : CompactCertificate where
  left := 151
  right := 152
  center := 303 / 2
  grid := fun i =>
    match i.val with
    | 0 => 48
    | 1 => 36
    | 2 => 57
    | 3 => 10
    | 4 => 28
    | 5 => 76
    | 6 => 56
    | 7 => 95
    | 8 => 70
    | 9 => 108
    | 10 => 62
    | 11 => 111
    | 12 => 103
    | 13 => 74
    | 14 => 84
    | 15 => 70
    | 16 => 62
    | 17 => 89
    | 18 => 49
    | 19 => 42
    | 20 => 26
    | 21 => 14
    | 22 => 38
    | 23 => 52
    | 24 => 22
    | 25 => 90
    | _ => 60
  point := fun i =>
    match i.val with
    | 0 => 303 / 2
    | 1 => 446376857214003 / 4000000000000
    | 2 => 144349104231699 / 800000000000
    | 3 => 130251653655321 / 4000000000000
    | 4 => 349874263128837 / 4000000000000
    | 5 => 949976684631729 / 4000000000000
    | 6 => 699748526257977 / 4000000000000
    | 7 => 1199031026574621 / 4000000000000
    | 8 => 883200827300439 / 4000000000000
    | 9 => 1355057194364697 / 4000000000000
    | 10 => 782342635933713 / 4000000000000
    | 11 => 1388280736266117 / 4000000000000
    | 12 => 1297111946860473 / 4000000000000
    | 13 => 925680290380809 / 4000000000000
    | 14 => 1049622789386511 / 4000000000000
    | 15 => 875066053113759 / 4000000000000
    | 16 => 773147396016939 / 4000000000000
    | 17 => 224088250232961 / 800000000000
    | 18 => 619839893262867 / 4000000000000
    | 19 => 525445142057787 / 4000000000000
    | 20 => 328799172699561 / 4000000000000
    | 21 => 176829288614487 / 4000000000000
    | 22 => 480125916784461 / 4000000000000
    | 23 => 655570892141997 / 4000000000000
    | 24 => 277200827300439 / 4000000000000
    | 25 => 1126805973246519 / 4000000000000
    | _ => 752654169360921 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))
    | 1 => (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))
    | 2 => (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000))
    | 3 => (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))
    | 4 => (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))
    | 5 => (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000))
    | 6 => (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))
    | 7 => (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))
    | 8 => (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000))
    | 9 => (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))
    | 10 => (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))
    | 11 => (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000))
    | 12 => (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))
    | 13 => (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))
    | 14 => (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
    | 15 => (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))
    | 16 => (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))
    | 17 => (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000))
    | 18 => (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))
    | 19 => (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))
    | 20 => (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000))
    | 21 => (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))
    | 22 => (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))
    | 23 => (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000))
    | 24 => (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))
    | 25 => (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))
    | _ => (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22226062242 / 1000000000000) (22226065118 / 1000000000000)
      | 1 => orderedInterval (1169860266 / 1000000000000) (1169860444 / 1000000000000)
      | 2 => orderedInterval (2523965685 / 1000000000000) (2523967032 / 1000000000000)
      | 3 => orderedInterval (6886039052 / 1000000000000) (6886045942 / 1000000000000)
      | 4 => orderedInterval (-379197193 / 1000000000000) (-379197076 / 1000000000000)
      | 5 => orderedInterval (740133791 / 1000000000000) (740135180 / 1000000000000)
      | 6 => orderedInterval (11948978182 / 1000000000000) (11948978398 / 1000000000000)
      | 7 => orderedInterval (-8131154847 / 1000000000000) (-8131154828 / 1000000000000)
      | _ => orderedInterval (-3314300583 / 1000000000000) (-3314300534 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4711827492 / 1000000000000) (4711830752 / 1000000000000)
      | 1 => orderedInterval (-3277754024 / 1000000000000) (-3277753787 / 1000000000000)
      | 2 => orderedInterval (-1601344153 / 1000000000000) (-1601341495 / 1000000000000)
      | 3 => orderedInterval (-25877018962 / 1000000000000) (-25877003199 / 1000000000000)
      | 4 => orderedInterval (7124685720 / 1000000000000) (7124685918 / 1000000000000)
      | 5 => orderedInterval (-2963834455 / 1000000000000) (-2963832679 / 1000000000000)
      | 6 => orderedInterval (-5424371453 / 1000000000000) (-5424371236 / 1000000000000)
      | 7 => orderedInterval (-1804880067 / 1000000000000) (-1804880050 / 1000000000000)
      | _ => orderedInterval (-18987917788 / 1000000000000) (-18987917716 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-21248668971 / 1000000000000) (-21248665189 / 1000000000000)
      | 1 => orderedInterval (-4400315936 / 1000000000000) (-4400315575 / 1000000000000)
      | 2 => orderedInterval (-7558745813 / 1000000000000) (-7558740545 / 1000000000000)
      | 3 => orderedInterval (-21318887131 / 1000000000000) (-21318850944 / 1000000000000)
      | 4 => orderedInterval (-1060421296 / 1000000000000) (-1060420958 / 1000000000000)
      | 5 => orderedInterval (1017606150 / 1000000000000) (1017608433 / 1000000000000)
      | 6 => orderedInterval (-10617583245 / 1000000000000) (-10617583024 / 1000000000000)
      | 7 => orderedInterval (6606404682 / 1000000000000) (6606404699 / 1000000000000)
      | _ => orderedInterval (3990136072 / 1000000000000) (3990136183 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5347578438 / 1000000000000) (-5347574025 / 1000000000000)
      | 1 => orderedInterval (12026895942 / 1000000000000) (12026896505 / 1000000000000)
      | 2 => orderedInterval (5963794195 / 1000000000000) (5963804603 / 1000000000000)
      | 3 => orderedInterval (131356555688 / 1000000000000) (131356638552 / 1000000000000)
      | 4 => orderedInterval (-16744157063 / 1000000000000) (-16744156486 / 1000000000000)
      | 5 => orderedInterval (5531399791 / 1000000000000) (5531402715 / 1000000000000)
      | 6 => orderedInterval (5062844549 / 1000000000000) (5062844773 / 1000000000000)
      | 7 => orderedInterval (1607645965 / 1000000000000) (1607645982 / 1000000000000)
      | _ => orderedInterval (42792817013 / 1000000000000) (42792817190 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19671008660 / 1000000000000) (19671013877 / 1000000000000)
      | 1 => orderedInterval (10239636409 / 1000000000000) (10239637292 / 1000000000000)
      | 2 => orderedInterval (24643532571 / 1000000000000) (24643553214 / 1000000000000)
      | 3 => orderedInterval (88252532468 / 1000000000000) (88252722779 / 1000000000000)
      | 4 => orderedInterval (11112223674 / 1000000000000) (11112224669 / 1000000000000)
      | 5 => orderedInterval (-9093761422 / 1000000000000) (-9093757655 / 1000000000000)
      | 6 => orderedInterval (10639153729 / 1000000000000) (10639153959 / 1000000000000)
      | 7 => orderedInterval (-7007744132 / 1000000000000) (-7007744114 / 1000000000000)
      | _ => orderedInterval (-150108065 / 1000000000000) (-150107769 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (33670386595 / 1000000000000) (33670399676 / 1000000000000)
    | 1 => orderedInterval (-48100607690 / 1000000000000) (-48100583492 / 1000000000000)
    | 2 => orderedInterval (-54590475488 / 1000000000000) (-54590426920 / 1000000000000)
    | 3 => orderedInterval (182250217642 / 1000000000000) (182250319809 / 1000000000000)
    | _ => orderedInterval (148306473892 / 1000000000000) (148306696252 / 1000000000000)

theorem compactCertificate277_stateChecks0 :
    compactCertificate277.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (303 / 2)) (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (446376857214003 / 4000000000000)) (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (144349104231699 / 800000000000)) (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks1 :
    compactCertificate277.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (130251653655321 / 4000000000000)) (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (349874263128837 / 4000000000000)) (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (949976684631729 / 4000000000000)) (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks2 :
    compactCertificate277.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (699748526257977 / 4000000000000)) (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1199031026574621 / 4000000000000)) (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (883200827300439 / 4000000000000)) (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks3 :
    compactCertificate277.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1355057194364697 / 4000000000000)) (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (782342635933713 / 4000000000000)) (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1388280736266117 / 4000000000000)) (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks4 :
    compactCertificate277.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1297111946860473 / 4000000000000)) (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (925680290380809 / 4000000000000)) (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1049622789386511 / 4000000000000)) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks5 :
    compactCertificate277.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875066053113759 / 4000000000000)) (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (773147396016939 / 4000000000000)) (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (224088250232961 / 800000000000)) (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks6 :
    compactCertificate277.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (619839893262867 / 4000000000000)) (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (525445142057787 / 4000000000000)) (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (328799172699561 / 4000000000000)) (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks7 :
    compactCertificate277.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (176829288614487 / 4000000000000)) (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (480125916784461 / 4000000000000)) (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (655570892141997 / 4000000000000)) (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_stateChecks8 :
    compactCertificate277.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (277200827300439 / 4000000000000)) (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1126805973246519 / 4000000000000)) (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (752654169360921 / 4000000000000)) (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_states : ∀ j,
    BesselStateValid (compactCertificate277.point j) (compactCertificate277.state j) :=
  compactCertificate277.statesValid_of_checks3 compactCertificate277_stateChecks0
    compactCertificate277_stateChecks1 compactCertificate277_stateChecks2
    compactCertificate277_stateChecks3 compactCertificate277_stateChecks4
    compactCertificate277_stateChecks5 compactCertificate277_stateChecks6
    compactCertificate277_stateChecks7 compactCertificate277_stateChecks8

theorem compactCertificate277_chunkChecks0_0 :
    compactCertificate277.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (303 / 2) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (446376857214003 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (144349104231699 / 800000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000)))) (orderedInterval (22226062242 / 1000000000000) (22226065118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (130251653655321 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (349874263128837 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (949976684631729 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000)))) (orderedInterval (1169860266 / 1000000000000) (1169860444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (699748526257977 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1199031026574621 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (883200827300439 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000)))) (orderedInterval (2523965685 / 1000000000000) (2523967032 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks0_1 :
    compactCertificate277.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1355057194364697 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (782342635933713 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1388280736266117 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000)))) (orderedInterval (6886039052 / 1000000000000) (6886045942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1297111946860473 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (925680290380809 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000)))) (orderedInterval (-379197193 / 1000000000000) (-379197076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (875066053113759 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (773147396016939 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (224088250232961 / 800000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000)))) (orderedInterval (740133791 / 1000000000000) (740135180 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks0_2 :
    compactCertificate277.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (619839893262867 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (525445142057787 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (328799172699561 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000)))) (orderedInterval (11948978182 / 1000000000000) (11948978398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (176829288614487 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (480125916784461 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (655570892141997 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000)))) (orderedInterval (-8131154847 / 1000000000000) (-8131154828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (277200827300439 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1126805973246519 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (752654169360921 / 4000000000000) 0 (IntervalRat.scale (303 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000)))) (orderedInterval (-3314300583 / 1000000000000) (-3314300534 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks0 :
    compactCertificate277.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate277.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate277_chunkChecks0_0
    compactCertificate277_chunkChecks0_1 compactCertificate277_chunkChecks0_2

theorem compactCertificate277_chunkChecks1_0 :
    compactCertificate277.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (303 / 2) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (446376857214003 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (144349104231699 / 800000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000)))) (orderedInterval (4711827492 / 1000000000000) (4711830752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (130251653655321 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (349874263128837 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (949976684631729 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000)))) (orderedInterval (-3277754024 / 1000000000000) (-3277753787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (699748526257977 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1199031026574621 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (883200827300439 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000)))) (orderedInterval (-1601344153 / 1000000000000) (-1601341495 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks1_1 :
    compactCertificate277.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1355057194364697 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (782342635933713 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1388280736266117 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000)))) (orderedInterval (-25877018962 / 1000000000000) (-25877003199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1297111946860473 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (925680290380809 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000)))) (orderedInterval (7124685720 / 1000000000000) (7124685918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (875066053113759 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (773147396016939 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (224088250232961 / 800000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000)))) (orderedInterval (-2963834455 / 1000000000000) (-2963832679 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks1_2 :
    compactCertificate277.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (619839893262867 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (525445142057787 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (328799172699561 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000)))) (orderedInterval (-5424371453 / 1000000000000) (-5424371236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (176829288614487 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (480125916784461 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (655570892141997 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000)))) (orderedInterval (-1804880067 / 1000000000000) (-1804880050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (277200827300439 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1126805973246519 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (752654169360921 / 4000000000000) 1 (IntervalRat.scale (303 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000)))) (orderedInterval (-18987917788 / 1000000000000) (-18987917716 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks1 :
    compactCertificate277.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate277.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate277_chunkChecks1_0
    compactCertificate277_chunkChecks1_1 compactCertificate277_chunkChecks1_2

theorem compactCertificate277_chunkChecks2_0 :
    compactCertificate277.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (303 / 2) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (446376857214003 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (144349104231699 / 800000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000)))) (orderedInterval (-21248668971 / 1000000000000) (-21248665189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (130251653655321 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (349874263128837 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (949976684631729 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000)))) (orderedInterval (-4400315936 / 1000000000000) (-4400315575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (699748526257977 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1199031026574621 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (883200827300439 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000)))) (orderedInterval (-7558745813 / 1000000000000) (-7558740545 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks2_1 :
    compactCertificate277.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1355057194364697 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (782342635933713 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1388280736266117 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000)))) (orderedInterval (-21318887131 / 1000000000000) (-21318850944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1297111946860473 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (925680290380809 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000)))) (orderedInterval (-1060421296 / 1000000000000) (-1060420958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (875066053113759 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (773147396016939 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (224088250232961 / 800000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000)))) (orderedInterval (1017606150 / 1000000000000) (1017608433 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks2_2 :
    compactCertificate277.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (619839893262867 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (525445142057787 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (328799172699561 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000)))) (orderedInterval (-10617583245 / 1000000000000) (-10617583024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (176829288614487 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (480125916784461 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (655570892141997 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000)))) (orderedInterval (6606404682 / 1000000000000) (6606404699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (277200827300439 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1126805973246519 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (752654169360921 / 4000000000000) 2 (IntervalRat.scale (303 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000)))) (orderedInterval (3990136072 / 1000000000000) (3990136183 / 1000000000000))) = true
  rfl'

theorem compactCertificate277_chunkChecks2 :
    compactCertificate277.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate277.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate277_chunkChecks2_0
    compactCertificate277_chunkChecks2_1 compactCertificate277_chunkChecks2_2

theorem compactCertificate277_chunkChecks3_0 :
    compactCertificate277.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (303 / 2) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (446376857214003 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (144349104231699 / 800000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000)))) (orderedInterval (-5347578438 / 1000000000000) (-5347574025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (130251653655321 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (349874263128837 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (949976684631729 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000)))) (orderedInterval (12026895942 / 1000000000000) (12026896505 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (699748526257977 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1199031026574621 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (883200827300439 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000)))) (orderedInterval (5963794195 / 1000000000000) (5963804603 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate277_chunkChecks3_1 :
    compactCertificate277.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1355057194364697 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (782342635933713 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1388280736266117 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000)))) (orderedInterval (131356555688 / 1000000000000) (131356638552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1297111946860473 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (925680290380809 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000)))) (orderedInterval (-16744157063 / 1000000000000) (-16744156486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (875066053113759 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (773147396016939 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (224088250232961 / 800000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000)))) (orderedInterval (5531399791 / 1000000000000) (5531402715 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate277_chunkChecks3_2 :
    compactCertificate277.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (619839893262867 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (525445142057787 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (328799172699561 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000)))) (orderedInterval (5062844549 / 1000000000000) (5062844773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (176829288614487 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (480125916784461 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (655570892141997 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000)))) (orderedInterval (1607645965 / 1000000000000) (1607645982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (277200827300439 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1126805973246519 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (752654169360921 / 4000000000000) 3 (IntervalRat.scale (303 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000)))) (orderedInterval (42792817013 / 1000000000000) (42792817190 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate277_chunkChecks3 :
    compactCertificate277.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate277.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate277_chunkChecks3_0
    compactCertificate277_chunkChecks3_1 compactCertificate277_chunkChecks3_2

theorem compactCertificate277_chunkChecks4_0 :
    compactCertificate277.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (303 / 2) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (64602123214 / 1000000000000) (64602123227 / 1000000000000), orderedInterval (5139719615 / 1000000000000) (5139719629 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (446376857214003 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49737338836 / 1000000000000) (-49737300100 / 1000000000000), orderedInterval (57064539046 / 1000000000000) (57064577781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (144349104231699 / 800000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49700846995 / 1000000000000) (-49700804403 / 1000000000000), orderedInterval (32665309531 / 1000000000000) (32665352124 / 1000000000000)))) (orderedInterval (19671008660 / 1000000000000) (19671013877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (130251653655321 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (130962540879 / 1000000000000) (130962543165 / 1000000000000), orderedInterval (-50975031130 / 1000000000000) (-50975028844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (349874263128837 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24226775645 / 1000000000000) (24226775646 / 1000000000000), orderedInterval (81662691491 / 1000000000000) (81662691492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (949976684631729 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23999970285 / 1000000000000) (-23999968400 / 1000000000000), orderedInterval (45926172883 / 1000000000000) (45926174769 / 1000000000000)))) (orderedInterval (10239636409 / 1000000000000) (10239637292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (699748526257977 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12420355969 / 1000000000000) (-12420355883 / 1000000000000), orderedInterval (59068396633 / 1000000000000) (59068396719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1199031026574621 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39978353759 / 1000000000000) (-39978310640 / 1000000000000), orderedInterval (22990715249 / 1000000000000) (22990758368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (883200827300439 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (53412495630 / 1000000000000) (53412495953 / 1000000000000), orderedInterval (-5628862115 / 1000000000000) (-5628861792 / 1000000000000)))) (orderedInterval (24643532571 / 1000000000000) (24643553214 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate277_chunkChecks4_1 :
    compactCertificate277.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1355057194364697 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11032226677 / 1000000000000) (11032226678 / 1000000000000), orderedInterval (41906655762 / 1000000000000) (41906655763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (782342635933713 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57039563798 / 1000000000000) (57039563887 / 1000000000000), orderedInterval (-1336819752 / 1000000000000) (-1336819662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1388280736266117 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32500729983 / 1000000000000) (32500777975 / 1000000000000), orderedInterval (-27938936324 / 1000000000000) (-27938888331 / 1000000000000)))) (orderedInterval (88252532468 / 1000000000000) (88252722779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1297111946860473 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44121161064 / 1000000000000) (-44121161019 / 1000000000000), orderedInterval (-3995504314 / 1000000000000) (-3995504269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (925680290380809 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14137689626 / 1000000000000) (-14137689482 / 1000000000000), orderedInterval (50538548837 / 1000000000000) (50538548982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000)))) (orderedInterval (11112223674 / 1000000000000) (11112224669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (875066053113759 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19010695880 / 1000000000000) (-19010695386 / 1000000000000), orderedInterval (50527519054 / 1000000000000) (50527519548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (773147396016939 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37284469526 / 1000000000000) (-37284445607 / 1000000000000), orderedInterval (43725825893 / 1000000000000) (43725849812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (224088250232961 / 800000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-45852373762 / 1000000000000) (-45852373760 / 1000000000000), orderedInterval (-12968187097 / 1000000000000) (-12968187095 / 1000000000000)))) (orderedInterval (-9093761422 / 1000000000000) (-9093757655 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate277_chunkChecks4_2 :
    compactCertificate277.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (619839893262867 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62323138113 / 1000000000000) (-62323137004 / 1000000000000), orderedInterval (15170818351 / 1000000000000) (15170819460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (525445142057787 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13751321244 / 1000000000000) (13751321245 / 1000000000000), orderedInterval (68191785187 / 1000000000000) (68191785188 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (328799172699561 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84849664126 / 1000000000000) (84849664127 / 1000000000000), orderedInterval (22833354495 / 1000000000000) (22833354496 / 1000000000000)))) (orderedInterval (10639153729 / 1000000000000) (10639153959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (176829288614487 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101465611879 / 1000000000000) (101465611880 / 1000000000000), orderedInterval (62923672776 / 1000000000000) (62923672777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (480125916784461 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (72159344003 / 1000000000000) (72159344008 / 1000000000000), orderedInterval (9535994225 / 1000000000000) (9535994230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (655570892141997 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (60289398363 / 1000000000000) (60289398364 / 1000000000000), orderedInterval (15612953155 / 1000000000000) (15612953156 / 1000000000000)))) (orderedInterval (-7007744132 / 1000000000000) (-7007744114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (277200827300439 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (78993670654 / 1000000000000) (78993670655 / 1000000000000), orderedInterval (53710100467 / 1000000000000) (53710100468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1126805973246519 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12078329685 / 1000000000000) (-12078329604 / 1000000000000), orderedInterval (45999978359 / 1000000000000) (45999978440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (752654169360921 / 4000000000000) 4 (IntervalRat.scale (303 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25442552754 / 1000000000000) (25442552755 / 1000000000000), orderedInterval (52239334022 / 1000000000000) (52239334023 / 1000000000000)))) (orderedInterval (-150108065 / 1000000000000) (-150107769 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate277_chunkChecks4 :
    compactCertificate277.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate277.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate277_chunkChecks4_0
    compactCertificate277_chunkChecks4_1 compactCertificate277_chunkChecks4_2

theorem compactCertificate277_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate277.chunkCheck r b = true :=
  compactCertificate277.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate277_chunkChecks0
    · exact compactCertificate277_chunkChecks1
    · exact compactCertificate277_chunkChecks2
    · exact compactCertificate277_chunkChecks3
    · exact compactCertificate277_chunkChecks4)

theorem compactCertificate277_coefficient0 :
    compactCertificate277.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate277_coefficient1 :
    compactCertificate277.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate277_coefficient2 :
    compactCertificate277.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate277_coefficient3 :
    compactCertificate277.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate277_coefficient4 :
    compactCertificate277.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate277_coefficients : ∀ r : Fin 5,
    compactCertificate277.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate277_coefficient0
  · exact compactCertificate277_coefficient1
  · exact compactCertificate277_coefficient2
  · exact compactCertificate277_coefficient3
  · exact compactCertificate277_coefficient4

theorem compactCertificate277_lower : (1 : ℚ) ≤ compactCertificate277.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate277, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate277_proves {t : ℝ} (ht : t ∈ compactCertificate277.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate277.proves compactCertificate277_states compactCertificate277_chunks
    compactCertificate277_coefficients compactCertificate277_lower ht

end Erdos232
