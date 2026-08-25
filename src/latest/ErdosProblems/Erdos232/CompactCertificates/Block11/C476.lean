/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate476 : CompactCertificate where
  left := 347
  right := 348
  center := 695 / 2
  grid := fun i =>
    match i.val with
    | 0 => 111
    | 1 => 82
    | 2 => 132
    | 3 => 24
    | 4 => 64
    | 5 => 173
    | 6 => 128
    | 7 => 219
    | 8 => 161
    | 9 => 247
    | 10 => 143
    | 11 => 254
    | 12 => 237
    | 13 => 169
    | 14 => 192
    | 15 => 160
    | 16 => 141
    | 17 => 205
    | 18 => 113
    | 19 => 96
    | 20 => 60
    | 21 => 32
    | 22 => 88
    | 23 => 120
    | 24 => 51
    | 25 => 206
    | _ => 137
  point := fun i =>
    match i.val with
    | 0 => 695 / 2
    | 1 => 204773541758239 / 800000000000
    | 2 => 66219556066687 / 160000000000
    | 3 => 59752408772573 / 800000000000
    | 4 => 160503374834681 / 800000000000
    | 5 => 435797885029077 / 800000000000
    | 6 => 321006749669501 / 800000000000
    | 7 => 550050536943473 / 800000000000
    | 8 => 405164735956307 / 800000000000
    | 9 => 621626897744861 / 800000000000
    | 10 => 358896456748469 / 800000000000
    | 11 => 636868060531321 / 800000000000
    | 12 => 595044754500349 / 800000000000
    | 13 => 424652014399117 / 800000000000
    | 14 => 481510124504043 / 800000000000
    | 15 => 401432941857467 / 800000000000
    | 16 => 354678178370807 / 800000000000
    | 17 => 102799560337893 / 160000000000
    | 18 => 284348993939071 / 800000000000
    | 19 => 241045791241031 / 800000000000
    | 20 => 150835264043693 / 800000000000
    | 21 => 81119706658131 / 800000000000
    | 22 => 220255783607393 / 800000000000
    | 23 => 300740442269761 / 800000000000
    | 24 => 127164735956307 / 800000000000
    | 25 => 516917591687347 / 800000000000
    | _ => 345276995185373 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))
    | 1 => (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))
    | 2 => (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000))
    | 3 => (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))
    | 4 => (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))
    | 5 => (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000))
    | 6 => (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))
    | 7 => (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))
    | 8 => (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000))
    | 9 => (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))
    | 10 => (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))
    | 11 => (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000))
    | 12 => (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))
    | 13 => (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))
    | 14 => (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000))
    | 15 => (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))
    | 16 => (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))
    | 17 => (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000))
    | 18 => (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))
    | 19 => (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))
    | 20 => (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000))
    | 21 => (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))
    | 22 => (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))
    | 23 => (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000))
    | 24 => (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))
    | 25 => (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))
    | _ => (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (6671672272 / 1000000000000) (6671673161 / 1000000000000)
      | 1 => orderedInterval (2804055184 / 1000000000000) (2804060847 / 1000000000000)
      | 2 => orderedInterval (-537417807 / 1000000000000) (-537417784 / 1000000000000)
      | 3 => orderedInterval (884315864 / 1000000000000) (884330523 / 1000000000000)
      | 4 => orderedInterval (-1937676867 / 1000000000000) (-1937676823 / 1000000000000)
      | 5 => orderedInterval (2508807605 / 1000000000000) (2508807730 / 1000000000000)
      | 6 => orderedInterval (6512143791 / 1000000000000) (6512143879 / 1000000000000)
      | 7 => orderedInterval (-205390428 / 1000000000000) (-205390373 / 1000000000000)
      | _ => orderedInterval (7375540345 / 1000000000000) (7375546017 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12454768937 / 1000000000000) (-12454768216 / 1000000000000)
      | 1 => orderedInterval (-816525160 / 1000000000000) (-816516301 / 1000000000000)
      | 2 => orderedInterval (1594609486 / 1000000000000) (1594609524 / 1000000000000)
      | 3 => orderedInterval (-2419659265 / 1000000000000) (-2419626118 / 1000000000000)
      | 4 => orderedInterval (-3033546983 / 1000000000000) (-3033546913 / 1000000000000)
      | 5 => orderedInterval (575952723 / 1000000000000) (575952940 / 1000000000000)
      | 6 => orderedInterval (1070379611 / 1000000000000) (1070379693 / 1000000000000)
      | 7 => orderedInterval (-4053480961 / 1000000000000) (-4053480912 / 1000000000000)
      | _ => orderedInterval (-8371673629 / 1000000000000) (-8371666582 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6765062757 / 1000000000000) (-6765062157 / 1000000000000)
      | 1 => orderedInterval (-5565356885 / 1000000000000) (-5565342981 / 1000000000000)
      | 2 => orderedInterval (577082544 / 1000000000000) (577082610 / 1000000000000)
      | 3 => orderedInterval (-4991465981 / 1000000000000) (-4991390897 / 1000000000000)
      | 4 => orderedInterval (4436105927 / 1000000000000) (4436106044 / 1000000000000)
      | 5 => orderedInterval (-5048015125 / 1000000000000) (-5048014742 / 1000000000000)
      | 6 => orderedInterval (-6130193845 / 1000000000000) (-6130193768 / 1000000000000)
      | 7 => orderedInterval (-1124288404 / 1000000000000) (-1124288357 / 1000000000000)
      | _ => orderedInterval (-12261484110 / 1000000000000) (-12261475312 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11430170447 / 1000000000000) (11430170959 / 1000000000000)
      | 1 => orderedInterval (3870568436 / 1000000000000) (3870590227 / 1000000000000)
      | 2 => orderedInterval (-6523468535 / 1000000000000) (-6523468417 / 1000000000000)
      | 3 => orderedInterval (-796574762 / 1000000000000) (-796404841 / 1000000000000)
      | 4 => orderedInterval (4691097063 / 1000000000000) (4691097260 / 1000000000000)
      | 5 => orderedInterval (770893339 / 1000000000000) (770894024 / 1000000000000)
      | 6 => orderedInterval (-1167253399 / 1000000000000) (-1167253323 / 1000000000000)
      | 7 => orderedInterval (4347259139 / 1000000000000) (4347259187 / 1000000000000)
      | _ => orderedInterval (21589641534 / 1000000000000) (21589652517 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (6777422749 / 1000000000000) (6777423199 / 1000000000000)
      | 1 => orderedInterval (13166191753 / 1000000000000) (13166225972 / 1000000000000)
      | 2 => orderedInterval (993773624 / 1000000000000) (993773839 / 1000000000000)
      | 3 => orderedInterval (22782451946 / 1000000000000) (22782837074 / 1000000000000)
      | 4 => orderedInterval (-10012598790 / 1000000000000) (-10012598448 / 1000000000000)
      | 5 => orderedInterval (11520296398 / 1000000000000) (11520297636 / 1000000000000)
      | 6 => orderedInterval (6382682728 / 1000000000000) (6382682803 / 1000000000000)
      | 7 => orderedInterval (1309780604 / 1000000000000) (1309780654 / 1000000000000)
      | _ => orderedInterval (22731252470 / 1000000000000) (22731266253 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (24076049959 / 1000000000000) (24076077177 / 1000000000000)
    | 1 => orderedInterval (-27908713115 / 1000000000000) (-27908662885 / 1000000000000)
    | 2 => orderedInterval (-36872678636 / 1000000000000) (-36872579560 / 1000000000000)
    | 3 => orderedInterval (38212333262 / 1000000000000) (38212537593 / 1000000000000)
    | _ => orderedInterval (75651253482 / 1000000000000) (75651688982 / 1000000000000)

theorem compactCertificate476_stateChecks0 :
    compactCertificate476.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (695 / 2)) (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (204773541758239 / 800000000000)) (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (66219556066687 / 160000000000)) (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks1 :
    compactCertificate476.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (59752408772573 / 800000000000)) (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (160503374834681 / 800000000000)) (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (435797885029077 / 800000000000)) (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks2 :
    compactCertificate476.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (321006749669501 / 800000000000)) (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (550050536943473 / 800000000000)) (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (405164735956307 / 800000000000)) (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks3 :
    compactCertificate476.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (621626897744861 / 800000000000)) (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (358896456748469 / 800000000000)) (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (636868060531321 / 800000000000)) (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks4 :
    compactCertificate476.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (595044754500349 / 800000000000)) (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (424652014399117 / 800000000000)) (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (481510124504043 / 800000000000)) (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks5 :
    compactCertificate476.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (401432941857467 / 800000000000)) (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (354678178370807 / 800000000000)) (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (102799560337893 / 160000000000)) (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks6 :
    compactCertificate476.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (284348993939071 / 800000000000)) (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241045791241031 / 800000000000)) (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (150835264043693 / 800000000000)) (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks7 :
    compactCertificate476.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (81119706658131 / 800000000000)) (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (220255783607393 / 800000000000)) (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (300740442269761 / 800000000000)) (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_stateChecks8 :
    compactCertificate476.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (127164735956307 / 800000000000)) (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (516917591687347 / 800000000000)) (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (345276995185373 / 800000000000)) (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_states : ∀ j,
    BesselStateValid (compactCertificate476.point j) (compactCertificate476.state j) :=
  compactCertificate476.statesValid_of_checks3 compactCertificate476_stateChecks0
    compactCertificate476_stateChecks1 compactCertificate476_stateChecks2
    compactCertificate476_stateChecks3 compactCertificate476_stateChecks4
    compactCertificate476_stateChecks5 compactCertificate476_stateChecks6
    compactCertificate476_stateChecks7 compactCertificate476_stateChecks8

theorem compactCertificate476_chunkChecks0_0 :
    compactCertificate476.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (695 / 2) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (204773541758239 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (66219556066687 / 160000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000)))) (orderedInterval (6671672272 / 1000000000000) (6671673161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (59752408772573 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (160503374834681 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (435797885029077 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000)))) (orderedInterval (2804055184 / 1000000000000) (2804060847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (321006749669501 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (550050536943473 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (405164735956307 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000)))) (orderedInterval (-537417807 / 1000000000000) (-537417784 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks0_1 :
    compactCertificate476.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (621626897744861 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (358896456748469 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (636868060531321 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000)))) (orderedInterval (884315864 / 1000000000000) (884330523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (595044754500349 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (424652014399117 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (481510124504043 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000)))) (orderedInterval (-1937676867 / 1000000000000) (-1937676823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (401432941857467 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (354678178370807 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (102799560337893 / 160000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000)))) (orderedInterval (2508807605 / 1000000000000) (2508807730 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks0_2 :
    compactCertificate476.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (284348993939071 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (241045791241031 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (150835264043693 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000)))) (orderedInterval (6512143791 / 1000000000000) (6512143879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (81119706658131 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (220255783607393 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (300740442269761 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000)))) (orderedInterval (-205390428 / 1000000000000) (-205390373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (127164735956307 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (516917591687347 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (345276995185373 / 800000000000) 0 (IntervalRat.scale (695 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000)))) (orderedInterval (7375540345 / 1000000000000) (7375546017 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks0 :
    compactCertificate476.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate476.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate476_chunkChecks0_0
    compactCertificate476_chunkChecks0_1 compactCertificate476_chunkChecks0_2

theorem compactCertificate476_chunkChecks1_0 :
    compactCertificate476.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (695 / 2) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (204773541758239 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (66219556066687 / 160000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000)))) (orderedInterval (-12454768937 / 1000000000000) (-12454768216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (59752408772573 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (160503374834681 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (435797885029077 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000)))) (orderedInterval (-816525160 / 1000000000000) (-816516301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (321006749669501 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (550050536943473 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (405164735956307 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000)))) (orderedInterval (1594609486 / 1000000000000) (1594609524 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks1_1 :
    compactCertificate476.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (621626897744861 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (358896456748469 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (636868060531321 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000)))) (orderedInterval (-2419659265 / 1000000000000) (-2419626118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (595044754500349 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (424652014399117 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (481510124504043 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000)))) (orderedInterval (-3033546983 / 1000000000000) (-3033546913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (401432941857467 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (354678178370807 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (102799560337893 / 160000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000)))) (orderedInterval (575952723 / 1000000000000) (575952940 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks1_2 :
    compactCertificate476.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (284348993939071 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (241045791241031 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (150835264043693 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000)))) (orderedInterval (1070379611 / 1000000000000) (1070379693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (81119706658131 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (220255783607393 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (300740442269761 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000)))) (orderedInterval (-4053480961 / 1000000000000) (-4053480912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (127164735956307 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (516917591687347 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (345276995185373 / 800000000000) 1 (IntervalRat.scale (695 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000)))) (orderedInterval (-8371673629 / 1000000000000) (-8371666582 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks1 :
    compactCertificate476.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate476.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate476_chunkChecks1_0
    compactCertificate476_chunkChecks1_1 compactCertificate476_chunkChecks1_2

theorem compactCertificate476_chunkChecks2_0 :
    compactCertificate476.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (695 / 2) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (204773541758239 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (66219556066687 / 160000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000)))) (orderedInterval (-6765062757 / 1000000000000) (-6765062157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (59752408772573 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (160503374834681 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (435797885029077 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000)))) (orderedInterval (-5565356885 / 1000000000000) (-5565342981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (321006749669501 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (550050536943473 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (405164735956307 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000)))) (orderedInterval (577082544 / 1000000000000) (577082610 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks2_1 :
    compactCertificate476.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (621626897744861 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (358896456748469 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (636868060531321 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000)))) (orderedInterval (-4991465981 / 1000000000000) (-4991390897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (595044754500349 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (424652014399117 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (481510124504043 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000)))) (orderedInterval (4436105927 / 1000000000000) (4436106044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (401432941857467 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (354678178370807 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (102799560337893 / 160000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000)))) (orderedInterval (-5048015125 / 1000000000000) (-5048014742 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks2_2 :
    compactCertificate476.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (284348993939071 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (241045791241031 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (150835264043693 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000)))) (orderedInterval (-6130193845 / 1000000000000) (-6130193768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (81119706658131 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (220255783607393 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (300740442269761 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000)))) (orderedInterval (-1124288404 / 1000000000000) (-1124288357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (127164735956307 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (516917591687347 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (345276995185373 / 800000000000) 2 (IntervalRat.scale (695 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000)))) (orderedInterval (-12261484110 / 1000000000000) (-12261475312 / 1000000000000))) = true
  rfl'

theorem compactCertificate476_chunkChecks2 :
    compactCertificate476.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate476.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate476_chunkChecks2_0
    compactCertificate476_chunkChecks2_1 compactCertificate476_chunkChecks2_2

theorem compactCertificate476_chunkChecks3_0 :
    compactCertificate476.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (695 / 2) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (204773541758239 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (66219556066687 / 160000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000)))) (orderedInterval (11430170447 / 1000000000000) (11430170959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (59752408772573 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (160503374834681 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (435797885029077 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000)))) (orderedInterval (3870568436 / 1000000000000) (3870590227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (321006749669501 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (550050536943473 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (405164735956307 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000)))) (orderedInterval (-6523468535 / 1000000000000) (-6523468417 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate476_chunkChecks3_1 :
    compactCertificate476.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (621626897744861 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (358896456748469 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (636868060531321 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000)))) (orderedInterval (-796574762 / 1000000000000) (-796404841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (595044754500349 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (424652014399117 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (481510124504043 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000)))) (orderedInterval (4691097063 / 1000000000000) (4691097260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (401432941857467 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (354678178370807 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (102799560337893 / 160000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000)))) (orderedInterval (770893339 / 1000000000000) (770894024 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate476_chunkChecks3_2 :
    compactCertificate476.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (284348993939071 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (241045791241031 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (150835264043693 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000)))) (orderedInterval (-1167253399 / 1000000000000) (-1167253323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (81119706658131 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (220255783607393 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (300740442269761 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000)))) (orderedInterval (4347259139 / 1000000000000) (4347259187 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (127164735956307 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (516917591687347 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (345276995185373 / 800000000000) 3 (IntervalRat.scale (695 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000)))) (orderedInterval (21589641534 / 1000000000000) (21589652517 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate476_chunkChecks3 :
    compactCertificate476.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate476.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate476_chunkChecks3_0
    compactCertificate476_chunkChecks3_1 compactCertificate476_chunkChecks3_2

theorem compactCertificate476_chunkChecks4_0 :
    compactCertificate476.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (695 / 2) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17910742152 / 1000000000000) (17910742687 / 1000000000000), orderedInterval (-38900002665 / 1000000000000) (-38900002129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (204773541758239 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37754011846 / 1000000000000) (-37753941872 / 1000000000000), orderedInterval (32658274251 / 1000000000000) (32658344225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (66219556066687 / 160000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1290444523 / 1000000000000) (-1290444522 / 1000000000000), orderedInterval (39200277512 / 1000000000000) (39200277514 / 1000000000000)))) (orderedInterval (6777422749 / 1000000000000) (6777423199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (59752408772573 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7010782580 / 1000000000000) (7010782583 / 1000000000000), orderedInterval (92009973037 / 1000000000000) (92009973040 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (160503374834681 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (19424714207 / 1000000000000) (19424714208 / 1000000000000), orderedInterval (52826953064 / 1000000000000) (52826953065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (435797885029077 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30537397353 / 1000000000000) (-30537318288 / 1000000000000), orderedInterval (15394212543 / 1000000000000) (15394291608 / 1000000000000)))) (orderedInterval (13166191753 / 1000000000000) (13166225972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (321006749669501 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3196468091 / 1000000000000) (-3196468089 / 1000000000000), orderedInterval (39707153953 / 1000000000000) (39707153956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (550050536943473 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10136007078 / 1000000000000) (-10136007077 / 1000000000000), orderedInterval (-28683548682 / 1000000000000) (-28683548681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (405164735956307 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35172619151 / 1000000000000) (-35172619047 / 1000000000000), orderedInterval (-4425714708 / 1000000000000) (-4425714605 / 1000000000000)))) (orderedInterval (993773624 / 1000000000000) (993773839 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate476_chunkChecks4_1 :
    compactCertificate476.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (621626897744861 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27550334904 / 1000000000000) (-27550293348 / 1000000000000), orderedInterval (7781406460 / 1000000000000) (7781448016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (358896456748469 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5924996816 / 1000000000000) (-5924996815 / 1000000000000), orderedInterval (-37194953408 / 1000000000000) (-37194953407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (636868060531321 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25127660875 / 1000000000000) (-25127610668 / 1000000000000), orderedInterval (12988416743 / 1000000000000) (12988466950 / 1000000000000)))) (orderedInterval (22782451946 / 1000000000000) (22782837074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (595044754500349 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-986148898 / 1000000000000) (-986148897 / 1000000000000), orderedInterval (-29238398000 / 1000000000000) (-29238397999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (424652014399117 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21533267340 / 1000000000000) (-21533267339 / 1000000000000), orderedInterval (-27102467667 / 1000000000000) (-27102467666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (481510124504043 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15960159255 / 1000000000000) (-15960158963 / 1000000000000), orderedInterval (28350139271 / 1000000000000) (28350139562 / 1000000000000)))) (orderedInterval (-10012598790 / 1000000000000) (-10012598448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (401432941857467 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2793135541 / 1000000000000) (-2793135539 / 1000000000000), orderedInterval (35511847449 / 1000000000000) (35511847451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (354678178370807 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34865146274 / 1000000000000) (-34865146272 / 1000000000000), orderedInterval (-14805166387 / 1000000000000) (-14805166385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (102799560337893 / 160000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21318795151 / 1000000000000) (21318798692 / 1000000000000), orderedInterval (-23176062362 / 1000000000000) (-23176058821 / 1000000000000)))) (orderedInterval (11520296398 / 1000000000000) (11520297636 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate476_chunkChecks4_2 :
    compactCertificate476.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (284348993939071 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39763054008 / 1000000000000) (-39763054007 / 1000000000000), orderedInterval (-14435176422 / 1000000000000) (-14435176420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (241045791241031 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22010058118 / 1000000000000) (22010058119 / 1000000000000), orderedInterval (40317138826 / 1000000000000) (40317138827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (150835264043693 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (43006871271 / 1000000000000) (43006871272 / 1000000000000), orderedInterval (38961666207 / 1000000000000) (38961666208 / 1000000000000)))) (orderedInterval (6382682728 / 1000000000000) (6382682803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (81119706658131 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78968911394 / 1000000000000) (78968911503 / 1000000000000), orderedInterval (-6882453673 / 1000000000000) (-6882453564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (220255783607393 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16735956077 / 1000000000000) (-16735955754 / 1000000000000), orderedInterval (45110358644 / 1000000000000) (45110358967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (300740442269761 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11392306132 / 1000000000000) (-11392306074 / 1000000000000), orderedInterval (39558667891 / 1000000000000) (39558667948 / 1000000000000)))) (orderedInterval (1309780604 / 1000000000000) (1309780654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (127164735956307 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29262610025 / 1000000000000) (29262612914 / 1000000000000), orderedInterval (-56205495853 / 1000000000000) (-56205492964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (516917591687347 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7335891636 / 1000000000000) (-7335891632 / 1000000000000), orderedInterval (30525183471 / 1000000000000) (30525183475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (345276995185373 / 800000000000) 4 (IntervalRat.scale (695 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35186851402 / 1000000000000) (-35186821783 / 1000000000000), orderedInterval (15432996645 / 1000000000000) (15433026263 / 1000000000000)))) (orderedInterval (22731252470 / 1000000000000) (22731266253 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate476_chunkChecks4 :
    compactCertificate476.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate476.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate476_chunkChecks4_0
    compactCertificate476_chunkChecks4_1 compactCertificate476_chunkChecks4_2

theorem compactCertificate476_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate476.chunkCheck r b = true :=
  compactCertificate476.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate476_chunkChecks0
    · exact compactCertificate476_chunkChecks1
    · exact compactCertificate476_chunkChecks2
    · exact compactCertificate476_chunkChecks3
    · exact compactCertificate476_chunkChecks4)

theorem compactCertificate476_coefficient0 :
    compactCertificate476.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate476_coefficient1 :
    compactCertificate476.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate476_coefficient2 :
    compactCertificate476.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate476_coefficient3 :
    compactCertificate476.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate476_coefficient4 :
    compactCertificate476.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate476_coefficients : ∀ r : Fin 5,
    compactCertificate476.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate476_coefficient0
  · exact compactCertificate476_coefficient1
  · exact compactCertificate476_coefficient2
  · exact compactCertificate476_coefficient3
  · exact compactCertificate476_coefficient4

theorem compactCertificate476_lower : (1 : ℚ) ≤ compactCertificate476.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate476, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate476_proves {t : ℝ} (ht : t ∈ compactCertificate476.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate476.proves compactCertificate476_states compactCertificate476_chunks
    compactCertificate476_coefficients compactCertificate476_lower ht

end Erdos232
