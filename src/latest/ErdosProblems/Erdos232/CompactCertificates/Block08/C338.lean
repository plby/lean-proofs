/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate338 : CompactCertificate where
  left := 210
  right := 211
  center := 421 / 2
  grid := fun i =>
    match i.val with
    | 0 => 67
    | 1 => 49
    | 2 => 80
    | 3 => 14
    | 4 => 39
    | 5 => 105
    | 6 => 77
    | 7 => 133
    | 8 => 98
    | 9 => 150
    | 10 => 87
    | 11 => 154
    | 12 => 143
    | 13 => 102
    | 14 => 116
    | 15 => 97
    | 16 => 86
    | 17 => 124
    | 18 => 69
    | 19 => 58
    | 20 => 36
    | 21 => 20
    | 22 => 53
    | 23 => 73
    | 24 => 31
    | 25 => 125
    | _ => 83
  point := fun i =>
    match i.val with
    | 0 => 421 / 2
    | 1 => 620213389066321 / 4000000000000
    | 2 => 200564266935793 / 800000000000
    | 3 => 180976720095347 / 4000000000000
    | 4 => 486128926657559 / 4000000000000
    | 5 => 1319934601419003 / 4000000000000
    | 6 => 972257853315539 / 4000000000000
    | 7 => 1665980403260447 / 4000000000000
    | 8 => 1227153624730973 / 4000000000000
    | 9 => 1882769237054579 / 4000000000000
    | 10 => 1087017325835291 / 4000000000000
    | 11 => 1928931320026519 / 4000000000000
    | 12 => 1802257853558611 / 4000000000000
    | 13 => 1286176245050563 / 4000000000000
    | 14 => 1458386779972677 / 4000000000000
    | 15 => 1215850852676213 / 4000000000000
    | 16 => 1074241101396473 / 4000000000000
    | 17 => 311356941742827 / 800000000000
    | 18 => 861229686678769 / 4000000000000
    | 19 => 730073943255209 / 4000000000000
    | 20 => 456846375269027 / 4000000000000
    | 21 => 245693500022109 / 4000000000000
    | 22 => 667105646753327 / 4000000000000
    | 23 => 910875728025679 / 4000000000000
    | 24 => 385153624730973 / 4000000000000
    | 25 => 1565628101441533 / 4000000000000
    | _ => 1045767014194547 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))
    | 1 => (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))
    | 2 => (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000))
    | 3 => (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))
    | 4 => (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))
    | 5 => (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000))
    | 6 => (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))
    | 7 => (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))
    | 8 => (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000))
    | 9 => (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))
    | 10 => (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))
    | 11 => (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000))
    | 12 => (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))
    | 13 => (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))
    | 14 => (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000))
    | 15 => (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))
    | 16 => (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))
    | 17 => (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000))
    | 18 => (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))
    | 19 => (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))
    | 20 => (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000))
    | 21 => (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))
    | 22 => (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))
    | 23 => (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000))
    | 24 => (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))
    | 25 => (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))
    | _ => (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15693388871 / 1000000000000) (-15693388825 / 1000000000000)
      | 1 => orderedInterval (1842795318 / 1000000000000) (1842795439 / 1000000000000)
      | 2 => orderedInterval (-960138444 / 1000000000000) (-960138383 / 1000000000000)
      | 3 => orderedInterval (-2683064872 / 1000000000000) (-2683060586 / 1000000000000)
      | 4 => orderedInterval (4411826406 / 1000000000000) (4411828721 / 1000000000000)
      | 5 => orderedInterval (2478175914 / 1000000000000) (2478178932 / 1000000000000)
      | 6 => orderedInterval (-6114959561 / 1000000000000) (-6114956821 / 1000000000000)
      | 7 => orderedInterval (-676505061 / 1000000000000) (-676499822 / 1000000000000)
      | _ => orderedInterval (7774469964 / 1000000000000) (7774470114 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11561643708 / 1000000000000) (-11561643668 / 1000000000000)
      | 1 => orderedInterval (1665394976 / 1000000000000) (1665395027 / 1000000000000)
      | 2 => orderedInterval (3565936832 / 1000000000000) (3565936948 / 1000000000000)
      | 3 => orderedInterval (-9134590522 / 1000000000000) (-9134583115 / 1000000000000)
      | 4 => orderedInterval (-2953349819 / 1000000000000) (-2953345270 / 1000000000000)
      | 5 => orderedInterval (-1418074438 / 1000000000000) (-1418070584 / 1000000000000)
      | 6 => orderedInterval (5179647682 / 1000000000000) (5179650440 / 1000000000000)
      | 7 => orderedInterval (3053328068 / 1000000000000) (3053333432 / 1000000000000)
      | _ => orderedInterval (6210774986 / 1000000000000) (6210775231 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15289260843 / 1000000000000) (15289260879 / 1000000000000)
      | 1 => orderedInterval (-6152308601 / 1000000000000) (-6152308555 / 1000000000000)
      | 2 => orderedInterval (3154188943 / 1000000000000) (3154189166 / 1000000000000)
      | 3 => orderedInterval (22767591839 / 1000000000000) (22767605729 / 1000000000000)
      | 4 => orderedInterval (-11480507393 / 1000000000000) (-11480498254 / 1000000000000)
      | 5 => orderedInterval (-4786362477 / 1000000000000) (-4786357536 / 1000000000000)
      | 6 => orderedInterval (7230022818 / 1000000000000) (7230025627 / 1000000000000)
      | 7 => orderedInterval (2633104080 / 1000000000000) (2633109819 / 1000000000000)
      | _ => orderedInterval (-8766315931 / 1000000000000) (-8766315513 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10100538432 / 1000000000000) (10100538467 / 1000000000000)
      | 1 => orderedInterval (-6927726832 / 1000000000000) (-6927726769 / 1000000000000)
      | 2 => orderedInterval (-11230916696 / 1000000000000) (-11230916264 / 1000000000000)
      | 3 => orderedInterval (32491241762 / 1000000000000) (32491269544 / 1000000000000)
      | 4 => orderedInterval (8742844290 / 1000000000000) (8742862903 / 1000000000000)
      | 5 => orderedInterval (-443560341 / 1000000000000) (-443554026 / 1000000000000)
      | 6 => orderedInterval (-6168374201 / 1000000000000) (-6168371342 / 1000000000000)
      | 7 => orderedInterval (-3776500956 / 1000000000000) (-3776494774 / 1000000000000)
      | _ => orderedInterval (-20049185055 / 1000000000000) (-20049184323 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14905185181 / 1000000000000) (-14905185145 / 1000000000000)
      | 1 => orderedInterval (14910841000 / 1000000000000) (14910841094 / 1000000000000)
      | 2 => orderedInterval (-11059460176 / 1000000000000) (-11059459334 / 1000000000000)
      | 3 => orderedInterval (-132696676432 / 1000000000000) (-132696617881 / 1000000000000)
      | 4 => orderedInterval (32418546087 / 1000000000000) (32418584568 / 1000000000000)
      | 5 => orderedInterval (10405897014 / 1000000000000) (10405905121 / 1000000000000)
      | 6 => orderedInterval (-7384079366 / 1000000000000) (-7384076436 / 1000000000000)
      | 7 => orderedInterval (-3579847304 / 1000000000000) (-3579840596 / 1000000000000)
      | _ => orderedInterval (3071976563 / 1000000000000) (3071977873 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9620789207 / 1000000000000) (-9620771231 / 1000000000000)
    | 1 => orderedInterval (-5392575943 / 1000000000000) (-5392551559 / 1000000000000)
    | 2 => orderedInterval (19888674121 / 1000000000000) (19888711362 / 1000000000000)
    | 3 => orderedInterval (2738360403 / 1000000000000) (2738423416 / 1000000000000)
    | _ => orderedInterval (-108817987795 / 1000000000000) (-108817870736 / 1000000000000)

theorem compactCertificate338_stateChecks0 :
    compactCertificate338.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (421 / 2)) (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (620213389066321 / 4000000000000)) (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (200564266935793 / 800000000000)) (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks1 :
    compactCertificate338.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (180976720095347 / 4000000000000)) (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (486128926657559 / 4000000000000)) (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319934601419003 / 4000000000000)) (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks2 :
    compactCertificate338.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (972257853315539 / 4000000000000)) (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1665980403260447 / 4000000000000)) (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1227153624730973 / 4000000000000)) (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks3 :
    compactCertificate338.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1882769237054579 / 4000000000000)) (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1087017325835291 / 4000000000000)) (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1928931320026519 / 4000000000000)) (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks4 :
    compactCertificate338.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1802257853558611 / 4000000000000)) (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1286176245050563 / 4000000000000)) (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1458386779972677 / 4000000000000)) (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks5 :
    compactCertificate338.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1215850852676213 / 4000000000000)) (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1074241101396473 / 4000000000000)) (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (311356941742827 / 800000000000)) (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks6 :
    compactCertificate338.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (861229686678769 / 4000000000000)) (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730073943255209 / 4000000000000)) (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (456846375269027 / 4000000000000)) (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks7 :
    compactCertificate338.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (245693500022109 / 4000000000000)) (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667105646753327 / 4000000000000)) (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (910875728025679 / 4000000000000)) (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_stateChecks8 :
    compactCertificate338.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (385153624730973 / 4000000000000)) (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1565628101441533 / 4000000000000)) (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1045767014194547 / 4000000000000)) (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_states : ∀ j,
    BesselStateValid (compactCertificate338.point j) (compactCertificate338.state j) :=
  compactCertificate338.statesValid_of_checks3 compactCertificate338_stateChecks0
    compactCertificate338_stateChecks1 compactCertificate338_stateChecks2
    compactCertificate338_stateChecks3 compactCertificate338_stateChecks4
    compactCertificate338_stateChecks5 compactCertificate338_stateChecks6
    compactCertificate338_stateChecks7 compactCertificate338_stateChecks8

theorem compactCertificate338_chunkChecks0_0 :
    compactCertificate338.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (421 / 2) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (620213389066321 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (200564266935793 / 800000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000)))) (orderedInterval (-15693388871 / 1000000000000) (-15693388825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (180976720095347 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (486128926657559 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1319934601419003 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000)))) (orderedInterval (1842795318 / 1000000000000) (1842795439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (972257853315539 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1665980403260447 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1227153624730973 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000)))) (orderedInterval (-960138444 / 1000000000000) (-960138383 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks0_1 :
    compactCertificate338.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1882769237054579 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1087017325835291 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1928931320026519 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000)))) (orderedInterval (-2683064872 / 1000000000000) (-2683060586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1802257853558611 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1286176245050563 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1458386779972677 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000)))) (orderedInterval (4411826406 / 1000000000000) (4411828721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1215850852676213 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1074241101396473 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (311356941742827 / 800000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000)))) (orderedInterval (2478175914 / 1000000000000) (2478178932 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks0_2 :
    compactCertificate338.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (861229686678769 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (730073943255209 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (456846375269027 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000)))) (orderedInterval (-6114959561 / 1000000000000) (-6114956821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (245693500022109 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (667105646753327 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (910875728025679 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000)))) (orderedInterval (-676505061 / 1000000000000) (-676499822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (385153624730973 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1565628101441533 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1045767014194547 / 4000000000000) 0 (IntervalRat.scale (421 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000)))) (orderedInterval (7774469964 / 1000000000000) (7774470114 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks0 :
    compactCertificate338.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate338.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate338_chunkChecks0_0
    compactCertificate338_chunkChecks0_1 compactCertificate338_chunkChecks0_2

theorem compactCertificate338_chunkChecks1_0 :
    compactCertificate338.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (421 / 2) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (620213389066321 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (200564266935793 / 800000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000)))) (orderedInterval (-11561643708 / 1000000000000) (-11561643668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (180976720095347 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (486128926657559 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1319934601419003 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000)))) (orderedInterval (1665394976 / 1000000000000) (1665395027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (972257853315539 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1665980403260447 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1227153624730973 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000)))) (orderedInterval (3565936832 / 1000000000000) (3565936948 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks1_1 :
    compactCertificate338.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1882769237054579 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1087017325835291 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1928931320026519 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000)))) (orderedInterval (-9134590522 / 1000000000000) (-9134583115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1802257853558611 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1286176245050563 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1458386779972677 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000)))) (orderedInterval (-2953349819 / 1000000000000) (-2953345270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1215850852676213 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1074241101396473 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (311356941742827 / 800000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000)))) (orderedInterval (-1418074438 / 1000000000000) (-1418070584 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks1_2 :
    compactCertificate338.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (861229686678769 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (730073943255209 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (456846375269027 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000)))) (orderedInterval (5179647682 / 1000000000000) (5179650440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (245693500022109 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (667105646753327 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (910875728025679 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000)))) (orderedInterval (3053328068 / 1000000000000) (3053333432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (385153624730973 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1565628101441533 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1045767014194547 / 4000000000000) 1 (IntervalRat.scale (421 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000)))) (orderedInterval (6210774986 / 1000000000000) (6210775231 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks1 :
    compactCertificate338.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate338.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate338_chunkChecks1_0
    compactCertificate338_chunkChecks1_1 compactCertificate338_chunkChecks1_2

theorem compactCertificate338_chunkChecks2_0 :
    compactCertificate338.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (421 / 2) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (620213389066321 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (200564266935793 / 800000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000)))) (orderedInterval (15289260843 / 1000000000000) (15289260879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (180976720095347 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (486128926657559 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1319934601419003 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000)))) (orderedInterval (-6152308601 / 1000000000000) (-6152308555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (972257853315539 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1665980403260447 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1227153624730973 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000)))) (orderedInterval (3154188943 / 1000000000000) (3154189166 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks2_1 :
    compactCertificate338.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1882769237054579 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1087017325835291 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1928931320026519 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000)))) (orderedInterval (22767591839 / 1000000000000) (22767605729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1802257853558611 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1286176245050563 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1458386779972677 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000)))) (orderedInterval (-11480507393 / 1000000000000) (-11480498254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1215850852676213 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1074241101396473 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (311356941742827 / 800000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000)))) (orderedInterval (-4786362477 / 1000000000000) (-4786357536 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks2_2 :
    compactCertificate338.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (861229686678769 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (730073943255209 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (456846375269027 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000)))) (orderedInterval (7230022818 / 1000000000000) (7230025627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (245693500022109 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (667105646753327 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (910875728025679 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000)))) (orderedInterval (2633104080 / 1000000000000) (2633109819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (385153624730973 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1565628101441533 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1045767014194547 / 4000000000000) 2 (IntervalRat.scale (421 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000)))) (orderedInterval (-8766315931 / 1000000000000) (-8766315513 / 1000000000000))) = true
  rfl'

theorem compactCertificate338_chunkChecks2 :
    compactCertificate338.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate338.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate338_chunkChecks2_0
    compactCertificate338_chunkChecks2_1 compactCertificate338_chunkChecks2_2

theorem compactCertificate338_chunkChecks3_0 :
    compactCertificate338.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (421 / 2) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (620213389066321 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (200564266935793 / 800000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000)))) (orderedInterval (10100538432 / 1000000000000) (10100538467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (180976720095347 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (486128926657559 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1319934601419003 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000)))) (orderedInterval (-6927726832 / 1000000000000) (-6927726769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (972257853315539 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1665980403260447 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1227153624730973 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000)))) (orderedInterval (-11230916696 / 1000000000000) (-11230916264 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate338_chunkChecks3_1 :
    compactCertificate338.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1882769237054579 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1087017325835291 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1928931320026519 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000)))) (orderedInterval (32491241762 / 1000000000000) (32491269544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1802257853558611 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1286176245050563 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1458386779972677 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000)))) (orderedInterval (8742844290 / 1000000000000) (8742862903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1215850852676213 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1074241101396473 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (311356941742827 / 800000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000)))) (orderedInterval (-443560341 / 1000000000000) (-443554026 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate338_chunkChecks3_2 :
    compactCertificate338.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (861229686678769 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (730073943255209 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (456846375269027 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000)))) (orderedInterval (-6168374201 / 1000000000000) (-6168371342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (245693500022109 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (667105646753327 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (910875728025679 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000)))) (orderedInterval (-3776500956 / 1000000000000) (-3776494774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (385153624730973 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1565628101441533 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1045767014194547 / 4000000000000) 3 (IntervalRat.scale (421 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000)))) (orderedInterval (-20049185055 / 1000000000000) (-20049184323 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate338_chunkChecks3 :
    compactCertificate338.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate338.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate338_chunkChecks3_0
    compactCertificate338_chunkChecks3_1 compactCertificate338_chunkChecks3_2

theorem compactCertificate338_chunkChecks4_0 :
    compactCertificate338.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (421 / 2) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39377106340 / 1000000000000) (-39377106339 / 1000000000000), orderedInterval (-38296118359 / 1000000000000) (-38296118358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (620213389066321 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60637626968 / 1000000000000) (-60637623770 / 1000000000000), orderedInterval (20904776405 / 1000000000000) (20904779603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (200564266935793 / 800000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8168598323 / 1000000000000) (8168598324 / 1000000000000), orderedInterval (49708889760 / 1000000000000) (49708889761 / 1000000000000)))) (orderedInterval (-14905185181 / 1000000000000) (-14905185145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (180976720095347 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105554078577 / 1000000000000) (105554086875 / 1000000000000), orderedInterval (-55282798095 / 1000000000000) (-55282789797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (486128926657559 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14769595598 / 1000000000000) (14769595721 / 1000000000000), orderedInterval (-70913984454 / 1000000000000) (-70913984332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1319934601419003 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-34445505404 / 1000000000000) (-34445505403 / 1000000000000), orderedInterval (-27201303605 / 1000000000000) (-27201303604 / 1000000000000)))) (orderedInterval (14910841000 / 1000000000000) (14910841094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (972257853315539 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47603834851 / 1000000000000) (-47603826530 / 1000000000000), orderedInterval (18886503531 / 1000000000000) (18886511852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1665980403260447 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20489207050 / 1000000000000) (20489208534 / 1000000000000), orderedInterval (-33321890436 / 1000000000000) (-33321888952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1227153624730973 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13578653697 / 1000000000000) (-13578653568 / 1000000000000), orderedInterval (43504686490 / 1000000000000) (43504686619 / 1000000000000)))) (orderedInterval (-11059460176 / 1000000000000) (-11059459334 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate338_chunkChecks4_1 :
    compactCertificate338.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1882769237054579 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8689863094 / 1000000000000) (8689863095 / 1000000000000), orderedInterval (35725973766 / 1000000000000) (35725973767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1087017325835291 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34014787739 / 1000000000000) (34014820024 / 1000000000000), orderedInterval (-34495473616 / 1000000000000) (-34495441331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1928931320026519 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25740733581 / 1000000000000) (-25740720851 / 1000000000000), orderedInterval (25669715978 / 1000000000000) (25669728708 / 1000000000000)))) (orderedInterval (-132696676432 / 1000000000000) (-132696617881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1802257853558611 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32412402272 / 1000000000000) (-32412310890 / 1000000000000), orderedInterval (19072121489 / 1000000000000) (19072212872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1286176245050563 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42295124646 / 1000000000000) (42295131404 / 1000000000000), orderedInterval (-13886179863 / 1000000000000) (-13886173105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1458386779972677 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34158961580 / 1000000000000) (34158961581 / 1000000000000), orderedInterval (24020932200 / 1000000000000) (24020932201 / 1000000000000)))) (orderedInterval (32418546087 / 1000000000000) (32418584568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1215850852676213 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-604656343 / 1000000000000) (-604656341 / 1000000000000), orderedInterval (-45759666412 / 1000000000000) (-45759666410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1074241101396473 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35985947351 / 1000000000000) (-35985894978 / 1000000000000), orderedInterval (32861851934 / 1000000000000) (32861904308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (311356941742827 / 800000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16630446007 / 1000000000000) (16630446008 / 1000000000000), orderedInterval (36845407575 / 1000000000000) (36845407576 / 1000000000000)))) (orderedInterval (10405897014 / 1000000000000) (10405905121 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate338_chunkChecks4_2 :
    compactCertificate338.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (861229686678769 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34092161005 / 1000000000000) (34092177294 / 1000000000000), orderedInterval (-42440954231 / 1000000000000) (-42440937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (730073943255209 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (52385788350 / 1000000000000) (52385788351 / 1000000000000), orderedInterval (27127281085 / 1000000000000) (27127281086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (456846375269027 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70684567843 / 1000000000000) (70684570361 / 1000000000000), orderedInterval (-24344569779 / 1000000000000) (-24344567261 / 1000000000000)))) (orderedInterval (-7384079366 / 1000000000000) (-7384076436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (245693500022109 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59574882857 / 1000000000000) (-59574862375 / 1000000000000), orderedInterval (83040327950 / 1000000000000) (83040348432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (667105646753327 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53795589049 / 1000000000000) (-53795589048 / 1000000000000), orderedInterval (-30223435153 / 1000000000000) (-30223435152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (910875728025679 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39105614714 / 1000000000000) (39105677804 / 1000000000000), orderedInterval (-35672211778 / 1000000000000) (-35672148688 / 1000000000000)))) (orderedInterval (-3579847304 / 1000000000000) (-3579840596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (385153624730973 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25335754236 / 1000000000000) (25335754855 / 1000000000000), orderedInterval (-77395810109 / 1000000000000) (-77395809490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1565628101441533 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19581594676 / 1000000000000) (19581595697 / 1000000000000), orderedInterval (-35281960786 / 1000000000000) (-35281959765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1045767014194547 / 4000000000000) 4 (IntervalRat.scale (421 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49117332155 / 1000000000000) (-49117332129 / 1000000000000), orderedInterval (-4651391908 / 1000000000000) (-4651391882 / 1000000000000)))) (orderedInterval (3071976563 / 1000000000000) (3071977873 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate338_chunkChecks4 :
    compactCertificate338.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate338.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate338_chunkChecks4_0
    compactCertificate338_chunkChecks4_1 compactCertificate338_chunkChecks4_2

theorem compactCertificate338_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate338.chunkCheck r b = true :=
  compactCertificate338.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate338_chunkChecks0
    · exact compactCertificate338_chunkChecks1
    · exact compactCertificate338_chunkChecks2
    · exact compactCertificate338_chunkChecks3
    · exact compactCertificate338_chunkChecks4)

theorem compactCertificate338_coefficient0 :
    compactCertificate338.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate338_coefficient1 :
    compactCertificate338.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate338_coefficient2 :
    compactCertificate338.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate338_coefficient3 :
    compactCertificate338.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate338_coefficient4 :
    compactCertificate338.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate338_coefficients : ∀ r : Fin 5,
    compactCertificate338.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate338_coefficient0
  · exact compactCertificate338_coefficient1
  · exact compactCertificate338_coefficient2
  · exact compactCertificate338_coefficient3
  · exact compactCertificate338_coefficient4

theorem compactCertificate338_lower : (1 : ℚ) ≤ compactCertificate338.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate338, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate338_proves {t : ℝ} (ht : t ∈ compactCertificate338.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate338.proves compactCertificate338_states compactCertificate338_chunks
    compactCertificate338_coefficients compactCertificate338_lower ht

end Erdos232
