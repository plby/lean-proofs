/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate443 : CompactCertificate where
  left := 314
  right := 315
  center := 629 / 2
  grid := fun i =>
    match i.val with
    | 0 => 100
    | 1 => 74
    | 2 => 119
    | 3 => 22
    | 4 => 58
    | 5 => 157
    | 6 => 116
    | 7 => 198
    | 8 => 146
    | 9 => 224
    | 10 => 129
    | 11 => 229
    | 12 => 214
    | 13 => 153
    | 14 => 173
    | 15 => 145
    | 16 => 128
    | 17 => 185
    | 18 => 102
    | 19 => 87
    | 20 => 54
    | 21 => 29
    | 22 => 79
    | 23 => 108
    | 24 => 46
    | 25 => 186
    | _ => 124
  point := fun i =>
    match i.val with
    | 0 => 629 / 2
    | 1 => 926637106229729 / 4000000000000
    | 2 => 299655401193857 / 800000000000
    | 3 => 270390396532003 / 4000000000000
    | 4 => 726306638640391 / 4000000000000
    | 5 => 1972063810671147 / 4000000000000
    | 6 => 1452613277281411 / 4000000000000
    | 7 => 2489077609621903 / 4000000000000
    | 8 => 1833443301557677 / 4000000000000
    | 9 => 2812973515694371 / 4000000000000
    | 10 => 1624071016509259 / 4000000000000
    | 11 => 2881942518519431 / 4000000000000
    | 12 => 2692684536551939 / 4000000000000
    | 13 => 1921626741417587 / 4000000000000
    | 14 => 2178919915921173 / 4000000000000
    | 15 => 1816556262074437 / 4000000000000
    | 16 => 1604982548167177 / 4000000000000
    | 17 => 465186499658523 / 800000000000
    | 18 => 1286730339479681 / 4000000000000
    | 19 => 1090775558925241 / 4000000000000
    | 20 => 682556698442323 / 4000000000000
    | 21 => 367081262503341 / 4000000000000
    | 22 => 996697035173023 / 4000000000000
    | 23 => 1360904591278271 / 4000000000000
    | 24 => 575443301557677 / 4000000000000
    | 25 => 2339145073175117 / 4000000000000
    | _ => 1562440503392803 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))
    | 1 => (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))
    | 2 => (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000))
    | 3 => (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))
    | 4 => (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))
    | 5 => (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000))
    | 6 => (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))
    | 7 => (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))
    | 8 => (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000))
    | 9 => (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))
    | 10 => (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))
    | 11 => (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000))
    | 12 => (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))
    | 13 => (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))
    | 14 => (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000))
    | 15 => (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))
    | 16 => (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))
    | 17 => (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000))
    | 18 => (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))
    | 19 => (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))
    | 20 => (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000))
    | 21 => (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))
    | 22 => (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))
    | 23 => (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000))
    | 24 => (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))
    | 25 => (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))
    | _ => (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13665396713 / 1000000000000) (13665396741 / 1000000000000)
      | 1 => orderedInterval (2406873294 / 1000000000000) (2406873914 / 1000000000000)
      | 2 => orderedInterval (-429607726 / 1000000000000) (-429607708 / 1000000000000)
      | 3 => orderedInterval (-8638975522 / 1000000000000) (-8638970795 / 1000000000000)
      | 4 => orderedInterval (-2132036605 / 1000000000000) (-2132036152 / 1000000000000)
      | 5 => orderedInterval (-286116880 / 1000000000000) (-286116823 / 1000000000000)
      | 6 => orderedInterval (-4008954491 / 1000000000000) (-4008950209 / 1000000000000)
      | 7 => orderedInterval (-629061527 / 1000000000000) (-629061368 / 1000000000000)
      | _ => orderedInterval (-9789594323 / 1000000000000) (-9789593137 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7825186450 / 1000000000000) (7825186483 / 1000000000000)
      | 1 => orderedInterval (4431675293 / 1000000000000) (4431675461 / 1000000000000)
      | 2 => orderedInterval (146150419 / 1000000000000) (146150450 / 1000000000000)
      | 3 => orderedInterval (-8858785641 / 1000000000000) (-8858774854 / 1000000000000)
      | 4 => orderedInterval (-4567880493 / 1000000000000) (-4567879684 / 1000000000000)
      | 5 => orderedInterval (-4155029158 / 1000000000000) (-4155029076 / 1000000000000)
      | 6 => orderedInterval (5318460600 / 1000000000000) (5318464959 / 1000000000000)
      | 7 => orderedInterval (403312149 / 1000000000000) (403312305 / 1000000000000)
      | _ => orderedInterval (1034185763 / 1000000000000) (1034187250 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12687629931 / 1000000000000) (-12687629893 / 1000000000000)
      | 1 => orderedInterval (-3546811189 / 1000000000000) (-3546811101 / 1000000000000)
      | 2 => orderedInterval (2416778344 / 1000000000000) (2416778399 / 1000000000000)
      | 3 => orderedInterval (34458236199 / 1000000000000) (34458260889 / 1000000000000)
      | 4 => orderedInterval (6129021041 / 1000000000000) (6129022500 / 1000000000000)
      | 5 => orderedInterval (1699628907 / 1000000000000) (1699629027 / 1000000000000)
      | 6 => orderedInterval (5768756399 / 1000000000000) (5768760859 / 1000000000000)
      | 7 => orderedInterval (3000721074 / 1000000000000) (3000721234 / 1000000000000)
      | _ => orderedInterval (20024359868 / 1000000000000) (20024361749 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-7542337736 / 1000000000000) (-7542337693 / 1000000000000)
      | 1 => orderedInterval (-8666273734 / 1000000000000) (-8666273638 / 1000000000000)
      | 2 => orderedInterval (1511165838 / 1000000000000) (1511165938 / 1000000000000)
      | 3 => orderedInterval (43123295010 / 1000000000000) (43123351492 / 1000000000000)
      | 4 => orderedInterval (10497647084 / 1000000000000) (10497649738 / 1000000000000)
      | 5 => orderedInterval (8328154805 / 1000000000000) (8328154984 / 1000000000000)
      | 6 => orderedInterval (-5062615825 / 1000000000000) (-5062611271 / 1000000000000)
      | 7 => orderedInterval (-524723214 / 1000000000000) (-524723048 / 1000000000000)
      | _ => orderedInterval (1724836418 / 1000000000000) (1724838810 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11281750072 / 1000000000000) (11281750123 / 1000000000000)
      | 1 => orderedInterval (8430699600 / 1000000000000) (8430699739 / 1000000000000)
      | 2 => orderedInterval (-11034780382 / 1000000000000) (-11034780197 / 1000000000000)
      | 3 => orderedInterval (-161431017824 / 1000000000000) (-161430888369 / 1000000000000)
      | 4 => orderedInterval (-19719966743 / 1000000000000) (-19719961858 / 1000000000000)
      | 5 => orderedInterval (-7121251345 / 1000000000000) (-7121251073 / 1000000000000)
      | 6 => orderedInterval (-6547990476 / 1000000000000) (-6547985808 / 1000000000000)
      | 7 => orderedInterval (-4033458183 / 1000000000000) (-4033458008 / 1000000000000)
      | _ => orderedInterval (-47709098219 / 1000000000000) (-47709095138 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9842077067 / 1000000000000) (-9842065537 / 1000000000000)
    | 1 => orderedInterval (1577275382 / 1000000000000) (1577293294 / 1000000000000)
    | 2 => orderedInterval (57263060712 / 1000000000000) (57263093663 / 1000000000000)
    | 3 => orderedInterval (43389148646 / 1000000000000) (43389215312 / 1000000000000)
    | _ => orderedInterval (-237885113500 / 1000000000000) (-237884970589 / 1000000000000)

theorem compactCertificate443_stateChecks0 :
    compactCertificate443.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (629 / 2)) (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (926637106229729 / 4000000000000)) (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (299655401193857 / 800000000000)) (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks1 :
    compactCertificate443.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (270390396532003 / 4000000000000)) (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (726306638640391 / 4000000000000)) (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1972063810671147 / 4000000000000)) (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks2 :
    compactCertificate443.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1452613277281411 / 4000000000000)) (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2489077609621903 / 4000000000000)) (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1833443301557677 / 4000000000000)) (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks3 :
    compactCertificate443.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2812973515694371 / 4000000000000)) (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1624071016509259 / 4000000000000)) (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2881942518519431 / 4000000000000)) (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks4 :
    compactCertificate443.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2692684536551939 / 4000000000000)) (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1921626741417587 / 4000000000000)) (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2178919915921173 / 4000000000000)) (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks5 :
    compactCertificate443.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1816556262074437 / 4000000000000)) (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1604982548167177 / 4000000000000)) (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (465186499658523 / 800000000000)) (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks6 :
    compactCertificate443.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1286730339479681 / 4000000000000)) (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1090775558925241 / 4000000000000)) (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (682556698442323 / 4000000000000)) (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks7 :
    compactCertificate443.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (367081262503341 / 4000000000000)) (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (996697035173023 / 4000000000000)) (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1360904591278271 / 4000000000000)) (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_stateChecks8 :
    compactCertificate443.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (575443301557677 / 4000000000000)) (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2339145073175117 / 4000000000000)) (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1562440503392803 / 4000000000000)) (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_states : ∀ j,
    BesselStateValid (compactCertificate443.point j) (compactCertificate443.state j) :=
  compactCertificate443.statesValid_of_checks3 compactCertificate443_stateChecks0
    compactCertificate443_stateChecks1 compactCertificate443_stateChecks2
    compactCertificate443_stateChecks3 compactCertificate443_stateChecks4
    compactCertificate443_stateChecks5 compactCertificate443_stateChecks6
    compactCertificate443_stateChecks7 compactCertificate443_stateChecks8

theorem compactCertificate443_chunkChecks0_0 :
    compactCertificate443.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (629 / 2) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (926637106229729 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (299655401193857 / 800000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000)))) (orderedInterval (13665396713 / 1000000000000) (13665396741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (270390396532003 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (726306638640391 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1972063810671147 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000)))) (orderedInterval (2406873294 / 1000000000000) (2406873914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1452613277281411 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2489077609621903 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1833443301557677 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000)))) (orderedInterval (-429607726 / 1000000000000) (-429607708 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks0_1 :
    compactCertificate443.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2812973515694371 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1624071016509259 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2881942518519431 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000)))) (orderedInterval (-8638975522 / 1000000000000) (-8638970795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2692684536551939 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1921626741417587 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2178919915921173 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000)))) (orderedInterval (-2132036605 / 1000000000000) (-2132036152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1816556262074437 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1604982548167177 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (465186499658523 / 800000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000)))) (orderedInterval (-286116880 / 1000000000000) (-286116823 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks0_2 :
    compactCertificate443.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1286730339479681 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1090775558925241 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (682556698442323 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000)))) (orderedInterval (-4008954491 / 1000000000000) (-4008950209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (367081262503341 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (996697035173023 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1360904591278271 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000)))) (orderedInterval (-629061527 / 1000000000000) (-629061368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (575443301557677 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2339145073175117 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1562440503392803 / 4000000000000) 0 (IntervalRat.scale (629 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000)))) (orderedInterval (-9789594323 / 1000000000000) (-9789593137 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks0 :
    compactCertificate443.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate443.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate443_chunkChecks0_0
    compactCertificate443_chunkChecks0_1 compactCertificate443_chunkChecks0_2

theorem compactCertificate443_chunkChecks1_0 :
    compactCertificate443.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (629 / 2) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (926637106229729 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (299655401193857 / 800000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000)))) (orderedInterval (7825186450 / 1000000000000) (7825186483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (270390396532003 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (726306638640391 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1972063810671147 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000)))) (orderedInterval (4431675293 / 1000000000000) (4431675461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1452613277281411 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2489077609621903 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1833443301557677 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000)))) (orderedInterval (146150419 / 1000000000000) (146150450 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks1_1 :
    compactCertificate443.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2812973515694371 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1624071016509259 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2881942518519431 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000)))) (orderedInterval (-8858785641 / 1000000000000) (-8858774854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2692684536551939 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1921626741417587 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2178919915921173 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000)))) (orderedInterval (-4567880493 / 1000000000000) (-4567879684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1816556262074437 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1604982548167177 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (465186499658523 / 800000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000)))) (orderedInterval (-4155029158 / 1000000000000) (-4155029076 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks1_2 :
    compactCertificate443.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1286730339479681 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1090775558925241 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (682556698442323 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000)))) (orderedInterval (5318460600 / 1000000000000) (5318464959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (367081262503341 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (996697035173023 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1360904591278271 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000)))) (orderedInterval (403312149 / 1000000000000) (403312305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (575443301557677 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2339145073175117 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1562440503392803 / 4000000000000) 1 (IntervalRat.scale (629 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000)))) (orderedInterval (1034185763 / 1000000000000) (1034187250 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks1 :
    compactCertificate443.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate443.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate443_chunkChecks1_0
    compactCertificate443_chunkChecks1_1 compactCertificate443_chunkChecks1_2

theorem compactCertificate443_chunkChecks2_0 :
    compactCertificate443.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (629 / 2) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (926637106229729 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (299655401193857 / 800000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000)))) (orderedInterval (-12687629931 / 1000000000000) (-12687629893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (270390396532003 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (726306638640391 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1972063810671147 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000)))) (orderedInterval (-3546811189 / 1000000000000) (-3546811101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1452613277281411 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2489077609621903 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1833443301557677 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000)))) (orderedInterval (2416778344 / 1000000000000) (2416778399 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks2_1 :
    compactCertificate443.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2812973515694371 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1624071016509259 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2881942518519431 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000)))) (orderedInterval (34458236199 / 1000000000000) (34458260889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2692684536551939 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1921626741417587 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2178919915921173 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000)))) (orderedInterval (6129021041 / 1000000000000) (6129022500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1816556262074437 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1604982548167177 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (465186499658523 / 800000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000)))) (orderedInterval (1699628907 / 1000000000000) (1699629027 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks2_2 :
    compactCertificate443.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1286730339479681 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1090775558925241 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (682556698442323 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000)))) (orderedInterval (5768756399 / 1000000000000) (5768760859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (367081262503341 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (996697035173023 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1360904591278271 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000)))) (orderedInterval (3000721074 / 1000000000000) (3000721234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (575443301557677 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2339145073175117 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1562440503392803 / 4000000000000) 2 (IntervalRat.scale (629 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000)))) (orderedInterval (20024359868 / 1000000000000) (20024361749 / 1000000000000))) = true
  rfl'

theorem compactCertificate443_chunkChecks2 :
    compactCertificate443.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate443.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate443_chunkChecks2_0
    compactCertificate443_chunkChecks2_1 compactCertificate443_chunkChecks2_2

theorem compactCertificate443_chunkChecks3_0 :
    compactCertificate443.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (629 / 2) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (926637106229729 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (299655401193857 / 800000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000)))) (orderedInterval (-7542337736 / 1000000000000) (-7542337693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (270390396532003 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (726306638640391 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1972063810671147 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000)))) (orderedInterval (-8666273734 / 1000000000000) (-8666273638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1452613277281411 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2489077609621903 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1833443301557677 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000)))) (orderedInterval (1511165838 / 1000000000000) (1511165938 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate443_chunkChecks3_1 :
    compactCertificate443.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2812973515694371 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1624071016509259 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2881942518519431 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000)))) (orderedInterval (43123295010 / 1000000000000) (43123351492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2692684536551939 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1921626741417587 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2178919915921173 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000)))) (orderedInterval (10497647084 / 1000000000000) (10497649738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1816556262074437 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1604982548167177 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (465186499658523 / 800000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000)))) (orderedInterval (8328154805 / 1000000000000) (8328154984 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate443_chunkChecks3_2 :
    compactCertificate443.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1286730339479681 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1090775558925241 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (682556698442323 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000)))) (orderedInterval (-5062615825 / 1000000000000) (-5062611271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (367081262503341 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (996697035173023 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1360904591278271 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000)))) (orderedInterval (-524723214 / 1000000000000) (-524723048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (575443301557677 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2339145073175117 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1562440503392803 / 4000000000000) 3 (IntervalRat.scale (629 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000)))) (orderedInterval (1724836418 / 1000000000000) (1724838810 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate443_chunkChecks3 :
    compactCertificate443.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate443.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate443_chunkChecks3_0
    compactCertificate443_chunkChecks3_1 compactCertificate443_chunkChecks3_2

theorem compactCertificate443_chunkChecks4_0 :
    compactCertificate443.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (629 / 2) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (40608532264 / 1000000000000) (40608532266 / 1000000000000), orderedInterval (19304841042 / 1000000000000) (19304841043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (926637106229729 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1767403629 / 1000000000000) (-1767403625 / 1000000000000), orderedInterval (52396269741 / 1000000000000) (52396269745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (299655401193857 / 800000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41136472633 / 1000000000000) (-41136472538 / 1000000000000), orderedInterval (-2664301786 / 1000000000000) (-2664301692 / 1000000000000)))) (orderedInterval (11281750072 / 1000000000000) (11281750123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (270390396532003 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64996509091 / 1000000000000) (-64996455473 / 1000000000000), orderedInterval (72545053588 / 1000000000000) (72545107207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (726306638640391 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8789706166 / 1000000000000) (8789706167 / 1000000000000), orderedInterval (58531922230 / 1000000000000) (58531922231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1972063810671147 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-19423087747 / 1000000000000) (-19423087746 / 1000000000000), orderedInterval (-30213067977 / 1000000000000) (-30213067976 / 1000000000000)))) (orderedInterval (8430699600 / 1000000000000) (8430699739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1452613277281411 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19570675103 / 1000000000000) (-19570674155 / 1000000000000), orderedInterval (37040762400 / 1000000000000) (37040763347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2489077609621903 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27242461081 / 1000000000000) (27242461082 / 1000000000000), orderedInterval (16738465754 / 1000000000000) (16738465755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1833443301557677 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16991820645 / 1000000000000) (16991820646 / 1000000000000), orderedInterval (33150483248 / 1000000000000) (33150483249 / 1000000000000)))) (orderedInterval (-11034780382 / 1000000000000) (-11034780197 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate443_chunkChecks4_1 :
    compactCertificate443.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2812973515694371 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9231322522 / 1000000000000) (9231322523 / 1000000000000), orderedInterval (28629868767 / 1000000000000) (28629868768 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1624071016509259 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39575374977 / 1000000000000) (-39575374793 / 1000000000000), orderedInterval (-1273741475 / 1000000000000) (-1273741291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2881942518519431 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28605717491 / 1000000000000) (-28605685217 / 1000000000000), orderedInterval (8101406873 / 1000000000000) (8101439147 / 1000000000000)))) (orderedInterval (-161431017824 / 1000000000000) (-161430888369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2692684536551939 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30641971484 / 1000000000000) (30641975360 / 1000000000000), orderedInterval (-2625053430 / 1000000000000) (-2625049554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1921626741417587 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18344634323 / 1000000000000) (-18344634322 / 1000000000000), orderedInterval (-31423603867 / 1000000000000) (-31423603866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2178919915921173 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30800282857 / 1000000000000) (-30800214721 / 1000000000000), orderedInterval (14861746120 / 1000000000000) (14861814256 / 1000000000000)))) (orderedInterval (-19719966743 / 1000000000000) (-19719961858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1816556262074437 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21348670719 / 1000000000000) (21348672955 / 1000000000000), orderedInterval (-30781452696 / 1000000000000) (-30781450460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1604982548167177 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3704453824 / 1000000000000) (-3704453821 / 1000000000000), orderedInterval (39664253313 / 1000000000000) (39664253316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (465186499658523 / 800000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29082928671 / 1000000000000) (-29082928669 / 1000000000000), orderedInterval (-15754845392 / 1000000000000) (-15754845391 / 1000000000000)))) (orderedInterval (-7121251345 / 1000000000000) (-7121251073 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate443_chunkChecks4_2 :
    compactCertificate443.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1286730339479681 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39973020652 / 1000000000000) (39973046765 / 1000000000000), orderedInterval (-19586127985 / 1000000000000) (-19586101872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1090775558925241 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7710627972 / 1000000000000) (-7710627971 / 1000000000000), orderedInterval (-47683956461 / 1000000000000) (-47683956460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (682556698442323 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59775647568 / 1000000000000) (59775648434 / 1000000000000), orderedInterval (-12731113854 / 1000000000000) (-12731112988 / 1000000000000)))) (orderedInterval (-6547990476 / 1000000000000) (-6547985808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (367081262503341 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82663148522 / 1000000000000) (-82663148517 / 1000000000000), orderedInterval (-9738013234 / 1000000000000) (-9738013229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (996697035173023 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49512928047 / 1000000000000) (-49512926735 / 1000000000000), orderedInterval (10267105140 / 1000000000000) (10267106452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1360904591278271 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42781672822 / 1000000000000) (42781674015 / 1000000000000), orderedInterval (-6457635699 / 1000000000000) (-6457634506 / 1000000000000)))) (orderedInterval (-4033458183 / 1000000000000) (-4033458008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (575443301557677 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8761577655 / 1000000000000) (8761577656 / 1000000000000), orderedInterval (65912767973 / 1000000000000) (65912767974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2339145073175117 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31154068720 / 1000000000000) (31154068728 / 1000000000000), orderedInterval (10838921050 / 1000000000000) (10838921058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1562440503392803 / 4000000000000) 4 (IntervalRat.scale (629 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38941264901 / 1000000000000) (38941270752 / 1000000000000), orderedInterval (-10698097251 / 1000000000000) (-10698091400 / 1000000000000)))) (orderedInterval (-47709098219 / 1000000000000) (-47709095138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate443_chunkChecks4 :
    compactCertificate443.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate443.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate443_chunkChecks4_0
    compactCertificate443_chunkChecks4_1 compactCertificate443_chunkChecks4_2

theorem compactCertificate443_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate443.chunkCheck r b = true :=
  compactCertificate443.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate443_chunkChecks0
    · exact compactCertificate443_chunkChecks1
    · exact compactCertificate443_chunkChecks2
    · exact compactCertificate443_chunkChecks3
    · exact compactCertificate443_chunkChecks4)

theorem compactCertificate443_coefficient0 :
    compactCertificate443.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate443_coefficient1 :
    compactCertificate443.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate443_coefficient2 :
    compactCertificate443.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate443_coefficient3 :
    compactCertificate443.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate443_coefficient4 :
    compactCertificate443.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate443_coefficients : ∀ r : Fin 5,
    compactCertificate443.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate443_coefficient0
  · exact compactCertificate443_coefficient1
  · exact compactCertificate443_coefficient2
  · exact compactCertificate443_coefficient3
  · exact compactCertificate443_coefficient4

theorem compactCertificate443_lower : (1 : ℚ) ≤ compactCertificate443.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate443, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate443_proves {t : ℝ} (ht : t ∈ compactCertificate443.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate443.proves compactCertificate443_states compactCertificate443_chunks
    compactCertificate443_coefficients compactCertificate443_lower ht

end Erdos232
