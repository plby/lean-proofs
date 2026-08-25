/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate425 : CompactCertificate where
  left := 296
  right := 297
  center := 593 / 2
  grid := fun i =>
    match i.val with
    | 0 => 94
    | 1 => 70
    | 2 => 112
    | 3 => 20
    | 4 => 55
    | 5 => 148
    | 6 => 109
    | 7 => 187
    | 8 => 138
    | 9 => 211
    | 10 => 122
    | 11 => 216
    | 12 => 202
    | 13 => 144
    | 14 => 164
    | 15 => 136
    | 16 => 120
    | 17 => 175
    | 18 => 97
    | 19 => 82
    | 20 => 51
    | 21 => 28
    | 22 => 75
    | 23 => 102
    | 24 => 43
    | 25 => 176
    | _ => 117
  point := fun i =>
    match i.val with
    | 0 => 593 / 2
    | 1 => 873602232105293 / 4000000000000
    | 2 => 282505012572269 / 800000000000
    | 3 => 254914952533351 / 4000000000000
    | 4 => 684737419258747 / 4000000000000
    | 5 => 1859195293685199 / 4000000000000
    | 6 => 1369474838518087 / 4000000000000
    | 7 => 2346618477751651 / 4000000000000
    | 8 => 1728508549799209 / 4000000000000
    | 9 => 2651976621314407 / 4000000000000
    | 10 => 1531119416200303 / 4000000000000
    | 11 => 2716998272626427 / 4000000000000
    | 12 => 2538572226033863 / 4000000000000
    | 13 => 1811644924738679 / 4000000000000
    | 14 => 2054212257776241 / 4000000000000
    | 15 => 1712588018140129 / 4000000000000
    | 16 => 1513123451610709 / 4000000000000
    | 17 => 438562153096191 / 800000000000
    | 18 => 1213085995725677 / 4000000000000
    | 19 => 1028346433136197 / 4000000000000
    | 20 => 643491450200791 / 4000000000000
    | 21 => 346071842073897 / 4000000000000
    | 22 => 939652371792691 / 4000000000000
    | 23 => 1283014980330707 / 4000000000000
    | 24 => 542508549799209 / 4000000000000
    | 25 => 2205267135759689 / 4000000000000
    | _ => 1473016245646951 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))
    | 1 => (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))
    | 2 => (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000))
    | 3 => (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))
    | 4 => (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))
    | 5 => (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000))
    | 6 => (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))
    | 7 => (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))
    | 8 => (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000))
    | 9 => (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))
    | 10 => (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))
    | 11 => (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000))
    | 12 => (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))
    | 13 => (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))
    | 14 => (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000))
    | 15 => (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))
    | 16 => (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))
    | 17 => (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000))
    | 18 => (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))
    | 19 => (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))
    | 20 => (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000))
    | 21 => (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))
    | 22 => (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))
    | 23 => (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000))
    | 24 => (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))
    | 25 => (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))
    | _ => (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18752075943 / 1000000000000) (18752084306 / 1000000000000)
      | 1 => orderedInterval (-998327575 / 1000000000000) (-998324926 / 1000000000000)
      | 2 => orderedInterval (-583286458 / 1000000000000) (-583286364 / 1000000000000)
      | 3 => orderedInterval (9510920888 / 1000000000000) (9510921058 / 1000000000000)
      | 4 => orderedInterval (3139744584 / 1000000000000) (3139744759 / 1000000000000)
      | 5 => orderedInterval (-992543572 / 1000000000000) (-992540259 / 1000000000000)
      | 6 => orderedInterval (-7351022019 / 1000000000000) (-7351020251 / 1000000000000)
      | 7 => orderedInterval (-1970001952 / 1000000000000) (-1970001437 / 1000000000000)
      | _ => orderedInterval (9382660763 / 1000000000000) (9382661853 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8371338909 / 1000000000000) (-8371330150 / 1000000000000)
      | 1 => orderedInterval (-4188044956 / 1000000000000) (-4188043407 / 1000000000000)
      | 2 => orderedInterval (3104280703 / 1000000000000) (3104280844 / 1000000000000)
      | 3 => orderedInterval (12536280159 / 1000000000000) (12536280522 / 1000000000000)
      | 4 => orderedInterval (381744204 / 1000000000000) (381744502 / 1000000000000)
      | 5 => orderedInterval (246490811 / 1000000000000) (246495183 / 1000000000000)
      | 6 => orderedInterval (3339668256 / 1000000000000) (3339670057 / 1000000000000)
      | 7 => orderedInterval (-1115777361 / 1000000000000) (-1115777188 / 1000000000000)
      | _ => orderedInterval (-2629090607 / 1000000000000) (-2629088625 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19798020848 / 1000000000000) (-19798011558 / 1000000000000)
      | 1 => orderedInterval (3321835108 / 1000000000000) (3321836041 / 1000000000000)
      | 2 => orderedInterval (1297649755 / 1000000000000) (1297649971 / 1000000000000)
      | 3 => orderedInterval (-45783128905 / 1000000000000) (-45783128109 / 1000000000000)
      | 4 => orderedInterval (-6473557684 / 1000000000000) (-6473557173 / 1000000000000)
      | 5 => orderedInterval (301326374 / 1000000000000) (301332236 / 1000000000000)
      | 6 => orderedInterval (5939700993 / 1000000000000) (5939702836 / 1000000000000)
      | 7 => orderedInterval (3416952813 / 1000000000000) (3416952887 / 1000000000000)
      | _ => orderedInterval (-18865183333 / 1000000000000) (-18865179693 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9147859881 / 1000000000000) (9147869789 / 1000000000000)
      | 1 => orderedInterval (8474845370 / 1000000000000) (8474845960 / 1000000000000)
      | 2 => orderedInterval (-10195742290 / 1000000000000) (-10195741957 / 1000000000000)
      | 3 => orderedInterval (-50368599036 / 1000000000000) (-50368597267 / 1000000000000)
      | 4 => orderedInterval (1124183422 / 1000000000000) (1124184302 / 1000000000000)
      | 5 => orderedInterval (1662296882 / 1000000000000) (1662304857 / 1000000000000)
      | 6 => orderedInterval (-4317667092 / 1000000000000) (-4317665210 / 1000000000000)
      | 7 => orderedInterval (1403116717 / 1000000000000) (1403116762 / 1000000000000)
      | _ => orderedInterval (10795782213 / 1000000000000) (10795788916 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (21154169926 / 1000000000000) (21154180621 / 1000000000000)
      | 1 => orderedInterval (-9216631574 / 1000000000000) (-9216631150 / 1000000000000)
      | 2 => orderedInterval (-2980549608 / 1000000000000) (-2980549085 / 1000000000000)
      | 3 => orderedInterval (229861164521 / 1000000000000) (229861168500 / 1000000000000)
      | 4 => orderedInterval (11037453295 / 1000000000000) (11037454822 / 1000000000000)
      | 5 => orderedInterval (3716752915 / 1000000000000) (3716764033 / 1000000000000)
      | 6 => orderedInterval (-5586724623 / 1000000000000) (-5586722694 / 1000000000000)
      | 7 => orderedInterval (-4125437997 / 1000000000000) (-4125437958 / 1000000000000)
      | _ => orderedInterval (42522200949 / 1000000000000) (42522213356 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (28890220602 / 1000000000000) (28890238739 / 1000000000000)
    | 1 => orderedInterval (3304212300 / 1000000000000) (3304231738 / 1000000000000)
    | 2 => orderedInterval (-76642425727 / 1000000000000) (-76642402562 / 1000000000000)
    | 3 => orderedInterval (-32273923933 / 1000000000000) (-32273893848 / 1000000000000)
    | _ => orderedInterval (286382397804 / 1000000000000) (286382440445 / 1000000000000)

theorem compactCertificate425_stateChecks0 :
    compactCertificate425.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (593 / 2)) (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (873602232105293 / 4000000000000)) (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (282505012572269 / 800000000000)) (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks1 :
    compactCertificate425.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (254914952533351 / 4000000000000)) (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (684737419258747 / 4000000000000)) (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1859195293685199 / 4000000000000)) (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks2 :
    compactCertificate425.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1369474838518087 / 4000000000000)) (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2346618477751651 / 4000000000000)) (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1728508549799209 / 4000000000000)) (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks3 :
    compactCertificate425.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2651976621314407 / 4000000000000)) (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1531119416200303 / 4000000000000)) (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2716998272626427 / 4000000000000)) (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks4 :
    compactCertificate425.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2538572226033863 / 4000000000000)) (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1811644924738679 / 4000000000000)) (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2054212257776241 / 4000000000000)) (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks5 :
    compactCertificate425.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1712588018140129 / 4000000000000)) (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1513123451610709 / 4000000000000)) (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (438562153096191 / 800000000000)) (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks6 :
    compactCertificate425.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1213085995725677 / 4000000000000)) (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028346433136197 / 4000000000000)) (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (643491450200791 / 4000000000000)) (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks7 :
    compactCertificate425.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (346071842073897 / 4000000000000)) (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (939652371792691 / 4000000000000)) (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1283014980330707 / 4000000000000)) (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_stateChecks8 :
    compactCertificate425.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (542508549799209 / 4000000000000)) (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2205267135759689 / 4000000000000)) (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1473016245646951 / 4000000000000)) (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_states : ∀ j,
    BesselStateValid (compactCertificate425.point j) (compactCertificate425.state j) :=
  compactCertificate425.statesValid_of_checks3 compactCertificate425_stateChecks0
    compactCertificate425_stateChecks1 compactCertificate425_stateChecks2
    compactCertificate425_stateChecks3 compactCertificate425_stateChecks4
    compactCertificate425_stateChecks5 compactCertificate425_stateChecks6
    compactCertificate425_stateChecks7 compactCertificate425_stateChecks8

theorem compactCertificate425_chunkChecks0_0 :
    compactCertificate425.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (593 / 2) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (873602232105293 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (282505012572269 / 800000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000)))) (orderedInterval (18752075943 / 1000000000000) (18752084306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (254914952533351 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (684737419258747 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1859195293685199 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000)))) (orderedInterval (-998327575 / 1000000000000) (-998324926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1369474838518087 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2346618477751651 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1728508549799209 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000)))) (orderedInterval (-583286458 / 1000000000000) (-583286364 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks0_1 :
    compactCertificate425.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2651976621314407 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1531119416200303 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2716998272626427 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000)))) (orderedInterval (9510920888 / 1000000000000) (9510921058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2538572226033863 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1811644924738679 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2054212257776241 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000)))) (orderedInterval (3139744584 / 1000000000000) (3139744759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1712588018140129 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1513123451610709 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (438562153096191 / 800000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000)))) (orderedInterval (-992543572 / 1000000000000) (-992540259 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks0_2 :
    compactCertificate425.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1213085995725677 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1028346433136197 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (643491450200791 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000)))) (orderedInterval (-7351022019 / 1000000000000) (-7351020251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (346071842073897 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (939652371792691 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1283014980330707 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000)))) (orderedInterval (-1970001952 / 1000000000000) (-1970001437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (542508549799209 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2205267135759689 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1473016245646951 / 4000000000000) 0 (IntervalRat.scale (593 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000)))) (orderedInterval (9382660763 / 1000000000000) (9382661853 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks0 :
    compactCertificate425.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate425.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate425_chunkChecks0_0
    compactCertificate425_chunkChecks0_1 compactCertificate425_chunkChecks0_2

theorem compactCertificate425_chunkChecks1_0 :
    compactCertificate425.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (593 / 2) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (873602232105293 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (282505012572269 / 800000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000)))) (orderedInterval (-8371338909 / 1000000000000) (-8371330150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (254914952533351 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (684737419258747 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1859195293685199 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000)))) (orderedInterval (-4188044956 / 1000000000000) (-4188043407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1369474838518087 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2346618477751651 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1728508549799209 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000)))) (orderedInterval (3104280703 / 1000000000000) (3104280844 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks1_1 :
    compactCertificate425.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2651976621314407 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1531119416200303 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2716998272626427 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000)))) (orderedInterval (12536280159 / 1000000000000) (12536280522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2538572226033863 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1811644924738679 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2054212257776241 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000)))) (orderedInterval (381744204 / 1000000000000) (381744502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1712588018140129 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1513123451610709 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (438562153096191 / 800000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000)))) (orderedInterval (246490811 / 1000000000000) (246495183 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks1_2 :
    compactCertificate425.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1213085995725677 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1028346433136197 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (643491450200791 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000)))) (orderedInterval (3339668256 / 1000000000000) (3339670057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (346071842073897 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (939652371792691 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1283014980330707 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000)))) (orderedInterval (-1115777361 / 1000000000000) (-1115777188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (542508549799209 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2205267135759689 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1473016245646951 / 4000000000000) 1 (IntervalRat.scale (593 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000)))) (orderedInterval (-2629090607 / 1000000000000) (-2629088625 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks1 :
    compactCertificate425.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate425.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate425_chunkChecks1_0
    compactCertificate425_chunkChecks1_1 compactCertificate425_chunkChecks1_2

theorem compactCertificate425_chunkChecks2_0 :
    compactCertificate425.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (593 / 2) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (873602232105293 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (282505012572269 / 800000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000)))) (orderedInterval (-19798020848 / 1000000000000) (-19798011558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (254914952533351 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (684737419258747 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1859195293685199 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000)))) (orderedInterval (3321835108 / 1000000000000) (3321836041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1369474838518087 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2346618477751651 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1728508549799209 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000)))) (orderedInterval (1297649755 / 1000000000000) (1297649971 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks2_1 :
    compactCertificate425.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2651976621314407 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1531119416200303 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2716998272626427 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000)))) (orderedInterval (-45783128905 / 1000000000000) (-45783128109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2538572226033863 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1811644924738679 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2054212257776241 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000)))) (orderedInterval (-6473557684 / 1000000000000) (-6473557173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1712588018140129 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1513123451610709 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (438562153096191 / 800000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000)))) (orderedInterval (301326374 / 1000000000000) (301332236 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks2_2 :
    compactCertificate425.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1213085995725677 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1028346433136197 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (643491450200791 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000)))) (orderedInterval (5939700993 / 1000000000000) (5939702836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (346071842073897 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (939652371792691 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1283014980330707 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000)))) (orderedInterval (3416952813 / 1000000000000) (3416952887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (542508549799209 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2205267135759689 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1473016245646951 / 4000000000000) 2 (IntervalRat.scale (593 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000)))) (orderedInterval (-18865183333 / 1000000000000) (-18865179693 / 1000000000000))) = true
  rfl'

theorem compactCertificate425_chunkChecks2 :
    compactCertificate425.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate425.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate425_chunkChecks2_0
    compactCertificate425_chunkChecks2_1 compactCertificate425_chunkChecks2_2

theorem compactCertificate425_chunkChecks3_0 :
    compactCertificate425.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (593 / 2) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (873602232105293 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (282505012572269 / 800000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000)))) (orderedInterval (9147859881 / 1000000000000) (9147869789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (254914952533351 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (684737419258747 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1859195293685199 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000)))) (orderedInterval (8474845370 / 1000000000000) (8474845960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1369474838518087 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2346618477751651 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1728508549799209 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000)))) (orderedInterval (-10195742290 / 1000000000000) (-10195741957 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate425_chunkChecks3_1 :
    compactCertificate425.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2651976621314407 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1531119416200303 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2716998272626427 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000)))) (orderedInterval (-50368599036 / 1000000000000) (-50368597267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2538572226033863 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1811644924738679 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2054212257776241 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000)))) (orderedInterval (1124183422 / 1000000000000) (1124184302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1712588018140129 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1513123451610709 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (438562153096191 / 800000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000)))) (orderedInterval (1662296882 / 1000000000000) (1662304857 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate425_chunkChecks3_2 :
    compactCertificate425.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1213085995725677 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1028346433136197 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (643491450200791 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000)))) (orderedInterval (-4317667092 / 1000000000000) (-4317665210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (346071842073897 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (939652371792691 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1283014980330707 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000)))) (orderedInterval (1403116717 / 1000000000000) (1403116762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (542508549799209 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2205267135759689 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1473016245646951 / 4000000000000) 3 (IntervalRat.scale (593 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000)))) (orderedInterval (10795782213 / 1000000000000) (10795788916 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate425_chunkChecks3 :
    compactCertificate425.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate425.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate425_chunkChecks3_0
    compactCertificate425_chunkChecks3_1 compactCertificate425_chunkChecks3_2

theorem compactCertificate425_chunkChecks4_0 :
    compactCertificate425.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (593 / 2) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42598046086 / 1000000000000) (42598060512 / 1000000000000), orderedInterval (-18306953808 / 1000000000000) (-18306939383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (873602232105293 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35847143921 / 1000000000000) (-35847118559 / 1000000000000), orderedInterval (40454102344 / 1000000000000) (40454127705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (282505012572269 / 800000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37520190514 / 1000000000000) (37520231202 / 1000000000000), orderedInterval (-19928198907 / 1000000000000) (-19928158219 / 1000000000000)))) (orderedInterval (21154169926 / 1000000000000) (21154180621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (254914952533351 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99347198215 / 1000000000000) (99347198339 / 1000000000000), orderedInterval (-11704533574 / 1000000000000) (-11704533450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (684737419258747 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44527848507 / 1000000000000) (44527920043 / 1000000000000), orderedInterval (-41797580264 / 1000000000000) (-41797508728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1859195293685199 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21750994450 / 1000000000000) (21750994451 / 1000000000000), orderedInterval (29919244149 / 1000000000000) (29919244150 / 1000000000000)))) (orderedInterval (-9216631574 / 1000000000000) (-9216631150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1369474838518087 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28438236754 / 1000000000000) (-28438236753 / 1000000000000), orderedInterval (-32373335361 / 1000000000000) (-32373335360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2346618477751651 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1252205285 / 1000000000000) (1252205286 / 1000000000000), orderedInterval (-32919177731 / 1000000000000) (-32919177730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1728508549799209 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22536528457 / 1000000000000) (-22536525276 / 1000000000000), orderedInterval (31095811852 / 1000000000000) (31095815032 / 1000000000000)))) (orderedInterval (-2980549608 / 1000000000000) (-2980549085 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate425_chunkChecks4_1 :
    compactCertificate425.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2651976621314407 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24336986107 / 1000000000000) (-24336986106 / 1000000000000), orderedInterval (-19163156175 / 1000000000000) (-19163156174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1531119416200303 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11685919816 / 1000000000000) (11685919817 / 1000000000000), orderedInterval (39056324241 / 1000000000000) (39056324242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2716998272626427 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30394110334 / 1000000000000) (30394110699 / 1000000000000), orderedInterval (3643368234 / 1000000000000) (3643368598 / 1000000000000)))) (orderedInterval (229861164521 / 1000000000000) (229861168500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2538572226033863 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23297688458 / 1000000000000) (23297688459 / 1000000000000), orderedInterval (21437002805 / 1000000000000) (21437002806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1811644924738679 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36194715762 / 1000000000000) (36194715771 / 1000000000000), orderedInterval (9735466115 / 1000000000000) (9735466123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2054212257776241 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27203199127 / 1000000000000) (-27203171942 / 1000000000000), orderedInterval (22378749260 / 1000000000000) (22378776445 / 1000000000000)))) (orderedInterval (11037453295 / 1000000000000) (11037454822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1712588018140129 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38349356829 / 1000000000000) (38349358034 / 1000000000000), orderedInterval (-4075227006 / 1000000000000) (-4075225801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1513123451610709 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35922205957 / 1000000000000) (35922258857 / 1000000000000), orderedInterval (-19859654654 / 1000000000000) (-19859601754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (438562153096191 / 800000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24227598869 / 1000000000000) (24227608339 / 1000000000000), orderedInterval (-23986838427 / 1000000000000) (-23986828957 / 1000000000000)))) (orderedInterval (3716752915 / 1000000000000) (3716764033 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate425_chunkChecks4_2 :
    compactCertificate425.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1213085995725677 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28738005609 / 1000000000000) (28738016198 / 1000000000000), orderedInterval (-35730738922 / 1000000000000) (-35730728333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1028346433136197 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12837268211 / 1000000000000) (12837268212 / 1000000000000), orderedInterval (48053030744 / 1000000000000) (48053030745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (643491450200791 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-62338340774 / 1000000000000) (-62338340767 / 1000000000000), orderedInterval (-8244135502 / 1000000000000) (-8244135495 / 1000000000000)))) (orderedInterval (-5586724623 / 1000000000000) (-5586722694 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (346071842073897 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52774285621 / 1000000000000) (-52774259640 / 1000000000000), orderedInterval (67929993045 / 1000000000000) (67930019025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (939652371792691 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4082861168 / 1000000000000) (-4082861167 / 1000000000000), orderedInterval (-51888890068 / 1000000000000) (-51888890067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1283014980330707 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39628873979 / 1000000000000) (39628873980 / 1000000000000), orderedInterval (20292898647 / 1000000000000) (20292898649 / 1000000000000)))) (orderedInterval (-4125437997 / 1000000000000) (-4125437958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (542508549799209 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66421293685 / 1000000000000) (-66421293684 / 1000000000000), orderedInterval (-16550384808 / 1000000000000) (-16550384807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2205267135759689 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24807009204 / 1000000000000) (-24806996958 / 1000000000000), orderedInterval (23246153429 / 1000000000000) (23246165675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1473016245646951 / 4000000000000) 4 (IntervalRat.scale (593 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41378672033 / 1000000000000) (-41378671976 / 1000000000000), orderedInterval (-4012659359 / 1000000000000) (-4012659302 / 1000000000000)))) (orderedInterval (42522200949 / 1000000000000) (42522213356 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate425_chunkChecks4 :
    compactCertificate425.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate425.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate425_chunkChecks4_0
    compactCertificate425_chunkChecks4_1 compactCertificate425_chunkChecks4_2

theorem compactCertificate425_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate425.chunkCheck r b = true :=
  compactCertificate425.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate425_chunkChecks0
    · exact compactCertificate425_chunkChecks1
    · exact compactCertificate425_chunkChecks2
    · exact compactCertificate425_chunkChecks3
    · exact compactCertificate425_chunkChecks4)

theorem compactCertificate425_coefficient0 :
    compactCertificate425.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate425_coefficient1 :
    compactCertificate425.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate425_coefficient2 :
    compactCertificate425.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate425_coefficient3 :
    compactCertificate425.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate425_coefficient4 :
    compactCertificate425.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate425_coefficients : ∀ r : Fin 5,
    compactCertificate425.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate425_coefficient0
  · exact compactCertificate425_coefficient1
  · exact compactCertificate425_coefficient2
  · exact compactCertificate425_coefficient3
  · exact compactCertificate425_coefficient4

theorem compactCertificate425_lower : (1 : ℚ) ≤ compactCertificate425.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate425, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate425_proves {t : ℝ} (ht : t ∈ compactCertificate425.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate425.proves compactCertificate425_states compactCertificate425_chunks
    compactCertificate425_coefficients compactCertificate425_lower ht

end Erdos232
