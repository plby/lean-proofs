/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate424 : CompactCertificate where
  left := 295
  right := 296
  center := 591 / 2
  grid := fun i =>
    match i.val with
    | 0 => 94
    | 1 => 69
    | 2 => 112
    | 3 => 20
    | 4 => 54
    | 5 => 148
    | 6 => 109
    | 7 => 186
    | 8 => 137
    | 9 => 210
    | 10 => 121
    | 11 => 216
    | 12 => 201
    | 13 => 144
    | 14 => 163
    | 15 => 136
    | 16 => 120
    | 17 => 174
    | 18 => 96
    | 19 => 82
    | 20 => 51
    | 21 => 27
    | 22 => 75
    | 23 => 102
    | 24 => 43
    | 25 => 175
    | _ => 117
  point := fun i =>
    match i.val with
    | 0 => 591 / 2
    | 1 => 870655850209491 / 4000000000000
    | 2 => 281552213204403 / 800000000000
    | 3 => 254055205644537 / 4000000000000
    | 4 => 682428018181989 / 4000000000000
    | 5 => 1852924820519313 / 4000000000000
    | 6 => 1364856036364569 / 4000000000000
    | 7 => 2338704081536637 / 4000000000000
    | 8 => 1722678841368183 / 4000000000000
    | 9 => 2643032349404409 / 4000000000000
    | 10 => 1525955438405361 / 4000000000000
    | 11 => 2707834703410149 / 4000000000000
    | 12 => 2530010431005081 / 4000000000000
    | 13 => 1805534823812073 / 4000000000000
    | 14 => 2047284054545967 / 4000000000000
    | 15 => 1706812004588223 / 4000000000000
    | 16 => 1508020168468683 / 4000000000000
    | 17 => 437083022731617 / 800000000000
    | 18 => 1208994643294899 / 4000000000000
    | 19 => 1024878148370139 / 4000000000000
    | 20 => 641321158631817 / 4000000000000
    | 21 => 344904652050039 / 4000000000000
    | 22 => 936483223827117 / 4000000000000
    | 23 => 1278687779722509 / 4000000000000
    | 24 => 540678841368183 / 4000000000000
    | 25 => 2197829472569943 / 4000000000000
    | _ => 1468048231327737 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))
    | 1 => (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))
    | 2 => (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000))
    | 3 => (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))
    | 4 => (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))
    | 5 => (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000))
    | 6 => (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))
    | 7 => (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))
    | 8 => (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000))
    | 9 => (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))
    | 10 => (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))
    | 11 => (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000))
    | 12 => (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))
    | 13 => (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))
    | 14 => (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000))
    | 15 => (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))
    | 16 => (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))
    | 17 => (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000))
    | 18 => (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))
    | 19 => (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))
    | 20 => (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000))
    | 21 => (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))
    | 22 => (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))
    | 23 => (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000))
    | 24 => (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))
    | 25 => (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))
    | _ => (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16631950101 / 1000000000000) (16631950126 / 1000000000000)
      | 1 => orderedInterval (3243464420 / 1000000000000) (3243468508 / 1000000000000)
      | 2 => orderedInterval (-1727349825 / 1000000000000) (-1727349808 / 1000000000000)
      | 3 => orderedInterval (-11153898416 / 1000000000000) (-11153887076 / 1000000000000)
      | 4 => orderedInterval (-133138506 / 1000000000000) (-133138145 / 1000000000000)
      | 5 => orderedInterval (-1162528119 / 1000000000000) (-1162528090 / 1000000000000)
      | 6 => orderedInterval (-7267688318 / 1000000000000) (-7267687872 / 1000000000000)
      | 7 => orderedInterval (470578251 / 1000000000000) (470579481 / 1000000000000)
      | _ => orderedInterval (2711918381 / 1000000000000) (2711918464 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12255583519 / 1000000000000) (12255583545 / 1000000000000)
      | 1 => orderedInterval (-2692760296 / 1000000000000) (-2692753924 / 1000000000000)
      | 2 => orderedInterval (-1531456743 / 1000000000000) (-1531456714 / 1000000000000)
      | 3 => orderedInterval (11701858899 / 1000000000000) (11701877660 / 1000000000000)
      | 4 => orderedInterval (5249352538 / 1000000000000) (5249353290 / 1000000000000)
      | 5 => orderedInterval (-46881298 / 1000000000000) (-46881256 / 1000000000000)
      | 6 => orderedInterval (-3668879865 / 1000000000000) (-3668879473 / 1000000000000)
      | 7 => orderedInterval (-3259375206 / 1000000000000) (-3259374587 / 1000000000000)
      | _ => orderedInterval (13928710132 / 1000000000000) (13928710248 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17698806060 / 1000000000000) (-17698806031 / 1000000000000)
      | 1 => orderedInterval (-5900733139 / 1000000000000) (-5900723148 / 1000000000000)
      | 2 => orderedInterval (5318682711 / 1000000000000) (5318682763 / 1000000000000)
      | 3 => orderedInterval (48043968782 / 1000000000000) (48044002345 / 1000000000000)
      | 4 => orderedInterval (-1012288164 / 1000000000000) (-1012286581 / 1000000000000)
      | 5 => orderedInterval (1092749060 / 1000000000000) (1092749122 / 1000000000000)
      | 6 => orderedInterval (6886999829 / 1000000000000) (6887000176 / 1000000000000)
      | 7 => orderedInterval (445012834 / 1000000000000) (445013228 / 1000000000000)
      | _ => orderedInterval (-7024167894 / 1000000000000) (-7024167723 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12980515462 / 1000000000000) (-12980515429 / 1000000000000)
      | 1 => orderedInterval (6098592466 / 1000000000000) (6098608117 / 1000000000000)
      | 2 => orderedInterval (4787156520 / 1000000000000) (4787156614 / 1000000000000)
      | 3 => orderedInterval (-53279717590 / 1000000000000) (-53279653328 / 1000000000000)
      | 4 => orderedInterval (-11720713970 / 1000000000000) (-11720710625 / 1000000000000)
      | 5 => orderedInterval (-2749780850 / 1000000000000) (-2749780755 / 1000000000000)
      | 6 => orderedInterval (2700113077 / 1000000000000) (2700113386 / 1000000000000)
      | 7 => orderedInterval (3905220447 / 1000000000000) (3905220736 / 1000000000000)
      | _ => orderedInterval (-30444121809 / 1000000000000) (-30444121546 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18998737730 / 1000000000000) (18998737768 / 1000000000000)
      | 1 => orderedInterval (13046892908 / 1000000000000) (13046917487 / 1000000000000)
      | 2 => orderedInterval (-17756482935 / 1000000000000) (-17756482761 / 1000000000000)
      | 3 => orderedInterval (-230132850150 / 1000000000000) (-230132719832 / 1000000000000)
      | 4 => orderedInterval (8285000993 / 1000000000000) (8285008094 / 1000000000000)
      | 5 => orderedInterval (911459472 / 1000000000000) (911459622 / 1000000000000)
      | 6 => orderedInterval (-7212247684 / 1000000000000) (-7212247407 / 1000000000000)
      | 7 => orderedInterval (-390148181 / 1000000000000) (-390147951 / 1000000000000)
      | _ => orderedInterval (19263064604 / 1000000000000) (19263065026 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1613307969 / 1000000000000) (1613325588 / 1000000000000)
    | 1 => orderedInterval (31936151680 / 1000000000000) (31936178789 / 1000000000000)
    | 2 => orderedInterval (30151417959 / 1000000000000) (30151464151 / 1000000000000)
    | 3 => orderedInterval (-93683767171 / 1000000000000) (-93683682830 / 1000000000000)
    | _ => orderedInterval (-194986573243 / 1000000000000) (-194986409954 / 1000000000000)

theorem compactCertificate424_stateChecks0 :
    compactCertificate424.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (591 / 2)) (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (870655850209491 / 4000000000000)) (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (281552213204403 / 800000000000)) (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks1 :
    compactCertificate424.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (254055205644537 / 4000000000000)) (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (682428018181989 / 4000000000000)) (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1852924820519313 / 4000000000000)) (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks2 :
    compactCertificate424.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1364856036364569 / 4000000000000)) (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2338704081536637 / 4000000000000)) (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1722678841368183 / 4000000000000)) (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks3 :
    compactCertificate424.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2643032349404409 / 4000000000000)) (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1525955438405361 / 4000000000000)) (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2707834703410149 / 4000000000000)) (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks4 :
    compactCertificate424.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2530010431005081 / 4000000000000)) (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1805534823812073 / 4000000000000)) (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2047284054545967 / 4000000000000)) (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks5 :
    compactCertificate424.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1706812004588223 / 4000000000000)) (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1508020168468683 / 4000000000000)) (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (437083022731617 / 800000000000)) (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks6 :
    compactCertificate424.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1208994643294899 / 4000000000000)) (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1024878148370139 / 4000000000000)) (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (641321158631817 / 4000000000000)) (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks7 :
    compactCertificate424.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (344904652050039 / 4000000000000)) (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (936483223827117 / 4000000000000)) (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278687779722509 / 4000000000000)) (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_stateChecks8 :
    compactCertificate424.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (540678841368183 / 4000000000000)) (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2197829472569943 / 4000000000000)) (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1468048231327737 / 4000000000000)) (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_states : ∀ j,
    BesselStateValid (compactCertificate424.point j) (compactCertificate424.state j) :=
  compactCertificate424.statesValid_of_checks3 compactCertificate424_stateChecks0
    compactCertificate424_stateChecks1 compactCertificate424_stateChecks2
    compactCertificate424_stateChecks3 compactCertificate424_stateChecks4
    compactCertificate424_stateChecks5 compactCertificate424_stateChecks6
    compactCertificate424_stateChecks7 compactCertificate424_stateChecks8

theorem compactCertificate424_chunkChecks0_0 :
    compactCertificate424.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (591 / 2) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (870655850209491 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (281552213204403 / 800000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000)))) (orderedInterval (16631950101 / 1000000000000) (16631950126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (254055205644537 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (682428018181989 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1852924820519313 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000)))) (orderedInterval (3243464420 / 1000000000000) (3243468508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1364856036364569 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2338704081536637 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1722678841368183 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000)))) (orderedInterval (-1727349825 / 1000000000000) (-1727349808 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks0_1 :
    compactCertificate424.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2643032349404409 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1525955438405361 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2707834703410149 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000)))) (orderedInterval (-11153898416 / 1000000000000) (-11153887076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2530010431005081 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1805534823812073 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2047284054545967 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000)))) (orderedInterval (-133138506 / 1000000000000) (-133138145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1706812004588223 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1508020168468683 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (437083022731617 / 800000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000)))) (orderedInterval (-1162528119 / 1000000000000) (-1162528090 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks0_2 :
    compactCertificate424.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1208994643294899 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1024878148370139 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (641321158631817 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000)))) (orderedInterval (-7267688318 / 1000000000000) (-7267687872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (344904652050039 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (936483223827117 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1278687779722509 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000)))) (orderedInterval (470578251 / 1000000000000) (470579481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (540678841368183 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2197829472569943 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1468048231327737 / 4000000000000) 0 (IntervalRat.scale (591 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000)))) (orderedInterval (2711918381 / 1000000000000) (2711918464 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks0 :
    compactCertificate424.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate424.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate424_chunkChecks0_0
    compactCertificate424_chunkChecks0_1 compactCertificate424_chunkChecks0_2

theorem compactCertificate424_chunkChecks1_0 :
    compactCertificate424.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (591 / 2) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (870655850209491 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (281552213204403 / 800000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000)))) (orderedInterval (12255583519 / 1000000000000) (12255583545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (254055205644537 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (682428018181989 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1852924820519313 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000)))) (orderedInterval (-2692760296 / 1000000000000) (-2692753924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1364856036364569 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2338704081536637 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1722678841368183 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000)))) (orderedInterval (-1531456743 / 1000000000000) (-1531456714 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks1_1 :
    compactCertificate424.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2643032349404409 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1525955438405361 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2707834703410149 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000)))) (orderedInterval (11701858899 / 1000000000000) (11701877660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2530010431005081 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1805534823812073 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2047284054545967 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000)))) (orderedInterval (5249352538 / 1000000000000) (5249353290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1706812004588223 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1508020168468683 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (437083022731617 / 800000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000)))) (orderedInterval (-46881298 / 1000000000000) (-46881256 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks1_2 :
    compactCertificate424.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1208994643294899 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1024878148370139 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (641321158631817 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000)))) (orderedInterval (-3668879865 / 1000000000000) (-3668879473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (344904652050039 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (936483223827117 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1278687779722509 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000)))) (orderedInterval (-3259375206 / 1000000000000) (-3259374587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (540678841368183 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2197829472569943 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1468048231327737 / 4000000000000) 1 (IntervalRat.scale (591 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000)))) (orderedInterval (13928710132 / 1000000000000) (13928710248 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks1 :
    compactCertificate424.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate424.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate424_chunkChecks1_0
    compactCertificate424_chunkChecks1_1 compactCertificate424_chunkChecks1_2

theorem compactCertificate424_chunkChecks2_0 :
    compactCertificate424.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (591 / 2) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (870655850209491 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (281552213204403 / 800000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000)))) (orderedInterval (-17698806060 / 1000000000000) (-17698806031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (254055205644537 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (682428018181989 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1852924820519313 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000)))) (orderedInterval (-5900733139 / 1000000000000) (-5900723148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1364856036364569 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2338704081536637 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1722678841368183 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000)))) (orderedInterval (5318682711 / 1000000000000) (5318682763 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks2_1 :
    compactCertificate424.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2643032349404409 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1525955438405361 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2707834703410149 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000)))) (orderedInterval (48043968782 / 1000000000000) (48044002345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2530010431005081 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1805534823812073 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2047284054545967 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000)))) (orderedInterval (-1012288164 / 1000000000000) (-1012286581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1706812004588223 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1508020168468683 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (437083022731617 / 800000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000)))) (orderedInterval (1092749060 / 1000000000000) (1092749122 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks2_2 :
    compactCertificate424.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1208994643294899 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1024878148370139 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (641321158631817 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000)))) (orderedInterval (6886999829 / 1000000000000) (6887000176 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (344904652050039 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (936483223827117 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1278687779722509 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000)))) (orderedInterval (445012834 / 1000000000000) (445013228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (540678841368183 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2197829472569943 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1468048231327737 / 4000000000000) 2 (IntervalRat.scale (591 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000)))) (orderedInterval (-7024167894 / 1000000000000) (-7024167723 / 1000000000000))) = true
  rfl'

theorem compactCertificate424_chunkChecks2 :
    compactCertificate424.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate424.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate424_chunkChecks2_0
    compactCertificate424_chunkChecks2_1 compactCertificate424_chunkChecks2_2

theorem compactCertificate424_chunkChecks3_0 :
    compactCertificate424.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (591 / 2) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (870655850209491 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (281552213204403 / 800000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000)))) (orderedInterval (-12980515462 / 1000000000000) (-12980515429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (254055205644537 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (682428018181989 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1852924820519313 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000)))) (orderedInterval (6098592466 / 1000000000000) (6098608117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1364856036364569 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2338704081536637 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1722678841368183 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000)))) (orderedInterval (4787156520 / 1000000000000) (4787156614 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate424_chunkChecks3_1 :
    compactCertificate424.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2643032349404409 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1525955438405361 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2707834703410149 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000)))) (orderedInterval (-53279717590 / 1000000000000) (-53279653328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2530010431005081 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1805534823812073 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2047284054545967 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000)))) (orderedInterval (-11720713970 / 1000000000000) (-11720710625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1706812004588223 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1508020168468683 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (437083022731617 / 800000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000)))) (orderedInterval (-2749780850 / 1000000000000) (-2749780755 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate424_chunkChecks3_2 :
    compactCertificate424.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1208994643294899 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1024878148370139 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (641321158631817 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000)))) (orderedInterval (2700113077 / 1000000000000) (2700113386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (344904652050039 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (936483223827117 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1278687779722509 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000)))) (orderedInterval (3905220447 / 1000000000000) (3905220736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (540678841368183 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2197829472569943 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1468048231327737 / 4000000000000) 3 (IntervalRat.scale (591 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000)))) (orderedInterval (-30444121809 / 1000000000000) (-30444121546 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate424_chunkChecks3 :
    compactCertificate424.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate424.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate424_chunkChecks3_0
    compactCertificate424_chunkChecks3_1 compactCertificate424_chunkChecks3_2

theorem compactCertificate424_chunkChecks4_0 :
    compactCertificate424.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (591 / 2) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38424937551 / 1000000000000) (38424937552 / 1000000000000), orderedInterval (25971585749 / 1000000000000) (25971585750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (870655850209491 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53765527292 / 1000000000000) (-53765526953 / 1000000000000), orderedInterval (5958157086 / 1000000000000) (5958157425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (281552213204403 / 800000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32423371756 / 1000000000000) (32423371757 / 1000000000000), orderedInterval (27478662136 / 1000000000000) (27478662137 / 1000000000000)))) (orderedInterval (18998737730 / 1000000000000) (18998737768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (254055205644537 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99559261870 / 1000000000000) (99559261875 / 1000000000000), orderedInterval (9750968317 / 1000000000000) (9750968322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (682428018181989 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60154245851 / 1000000000000) (60154246436 / 1000000000000), orderedInterval (-10804090184 / 1000000000000) (-10804089599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1852924820519313 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29923900267 / 1000000000000) (-29923843563 / 1000000000000), orderedInterval (21915232177 / 1000000000000) (21915288881 / 1000000000000)))) (orderedInterval (13046892908 / 1000000000000) (13046917487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1364856036364569 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18185222447 / 1000000000000) (18185223024 / 1000000000000), orderedInterval (-39206339088 / 1000000000000) (-39206338510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2338704081536637 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29772254326 / 1000000000000) (29772254328 / 1000000000000), orderedInterval (14203192410 / 1000000000000) (14203192412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1722678841368183 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33476227665 / 1000000000000) (-33476227664 / 1000000000000), orderedInterval (-18870140680 / 1000000000000) (-18870140679 / 1000000000000)))) (orderedInterval (-17756482935 / 1000000000000) (-17756482761 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate424_chunkChecks4_1 :
    compactCertificate424.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2643032349404409 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30164499890 / 1000000000000) (30164517063 / 1000000000000), orderedInterval (-7342050295 / 1000000000000) (-7342033122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1525955438405361 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34382924938 / 1000000000000) (-34382830116 / 1000000000000), orderedInterval (22103888178 / 1000000000000) (22103983000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2707834703410149 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22837858040 / 1000000000000) (-22837849980 / 1000000000000), orderedInterval (20482541574 / 1000000000000) (20482549635 / 1000000000000)))) (orderedInterval (-230132850150 / 1000000000000) (-230132719832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2530010431005081 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30684467528 / 1000000000000) (-30684449597 / 1000000000000), orderedInterval (8084832753 / 1000000000000) (8084850683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1805534823812073 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8214469669 / 1000000000000) (-8214469657 / 1000000000000), orderedInterval (36654659828 / 1000000000000) (36654659841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2047284054545967 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17724523667 / 1000000000000) (-17724523666 / 1000000000000), orderedInterval (-30473246839 / 1000000000000) (-30473246838 / 1000000000000)))) (orderedInterval (8285000993 / 1000000000000) (8285008094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1706812004588223 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8862414614 / 1000000000000) (8862414615 / 1000000000000), orderedInterval (37584948240 / 1000000000000) (37584948241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1508020168468683 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29449285497 / 1000000000000) (29449285498 / 1000000000000), orderedInterval (28620384388 / 1000000000000) (28620384389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (437083022731617 / 800000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419982286 / 1000000000000) (16419982287 / 1000000000000), orderedInterval (29911545383 / 1000000000000) (29911545384 / 1000000000000)))) (orderedInterval (911459472 / 1000000000000) (911459622 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate424_chunkChecks4_2 :
    compactCertificate424.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1208994643294899 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45506643890 / 1000000000000) (45506643912 / 1000000000000), orderedInterval (5876257610 / 1000000000000) (5876257632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1024878148370139 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28397865254 / 1000000000000) (-28397858743 / 1000000000000), orderedInterval (41021598399 / 1000000000000) (41021604911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (641321158631817 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49111476115 / 1000000000000) (-49111476114 / 1000000000000), orderedInterval (-39327670436 / 1000000000000) (-39327670435 / 1000000000000)))) (orderedInterval (-7212247684 / 1000000000000) (-7212247407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (344904652050039 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70115663605 / 1000000000000) (-70115624738 / 1000000000000), orderedInterval (50074386394 / 1000000000000) (50074425261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (936483223827117 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34139591638 / 1000000000000) (34139612622 / 1000000000000), orderedInterval (-39489692082 / 1000000000000) (-39489671098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1278687779722509 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (647116337 / 1000000000000) (647116338 / 1000000000000), orderedInterval (44620306428 / 1000000000000) (44620306429 / 1000000000000)))) (orderedInterval (-390148181 / 1000000000000) (-390147951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (540678841368183 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52263282605 / 1000000000000) (-52263282604 / 1000000000000), orderedInterval (-44285048284 / 1000000000000) (-44285048283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2197829472569943 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15227952737 / 1000000000000) (-15227952736 / 1000000000000), orderedInterval (-30428602408 / 1000000000000) (-30428602407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1468048231327737 / 4000000000000) 4 (IntervalRat.scale (591 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9526351355 / 1000000000000) (-9526351354 / 1000000000000), orderedInterval (-40531464804 / 1000000000000) (-40531464803 / 1000000000000)))) (orderedInterval (19263064604 / 1000000000000) (19263065026 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate424_chunkChecks4 :
    compactCertificate424.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate424.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate424_chunkChecks4_0
    compactCertificate424_chunkChecks4_1 compactCertificate424_chunkChecks4_2

theorem compactCertificate424_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate424.chunkCheck r b = true :=
  compactCertificate424.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate424_chunkChecks0
    · exact compactCertificate424_chunkChecks1
    · exact compactCertificate424_chunkChecks2
    · exact compactCertificate424_chunkChecks3
    · exact compactCertificate424_chunkChecks4)

theorem compactCertificate424_coefficient0 :
    compactCertificate424.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate424_coefficient1 :
    compactCertificate424.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate424_coefficient2 :
    compactCertificate424.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate424_coefficient3 :
    compactCertificate424.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate424_coefficient4 :
    compactCertificate424.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate424_coefficients : ∀ r : Fin 5,
    compactCertificate424.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate424_coefficient0
  · exact compactCertificate424_coefficient1
  · exact compactCertificate424_coefficient2
  · exact compactCertificate424_coefficient3
  · exact compactCertificate424_coefficient4

theorem compactCertificate424_lower : (1 : ℚ) ≤ compactCertificate424.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate424, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate424_proves {t : ℝ} (ht : t ∈ compactCertificate424.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate424.proves compactCertificate424_states compactCertificate424_chunks
    compactCertificate424_coefficients compactCertificate424_lower ht

end Erdos232
