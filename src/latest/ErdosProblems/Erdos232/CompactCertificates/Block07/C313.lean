/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate313 : CompactCertificate where
  left := 186
  right := 187
  center := 373 / 2
  grid := fun i =>
    match i.val with
    | 0 => 59
    | 1 => 44
    | 2 => 71
    | 3 => 13
    | 4 => 34
    | 5 => 93
    | 6 => 69
    | 7 => 118
    | 8 => 87
    | 9 => 133
    | 10 => 77
    | 11 => 136
    | 12 => 127
    | 13 => 91
    | 14 => 103
    | 15 => 86
    | 16 => 76
    | 17 => 110
    | 18 => 61
    | 19 => 51
    | 20 => 32
    | 21 => 17
    | 22 => 47
    | 23 => 64
    | 24 => 27
    | 25 => 110
    | _ => 74
  point := fun i =>
    match i.val with
    | 0 => 373 / 2
    | 1 => 549500223567073 / 4000000000000
    | 2 => 177697082107009 / 800000000000
    | 3 => 160342794763811 / 4000000000000
    | 4 => 430703300815367 / 4000000000000
    | 5 => 1169443245437739 / 4000000000000
    | 6 => 861406601631107 / 4000000000000
    | 7 => 1476034894100111 / 4000000000000
    | 8 => 1087240622386349 / 4000000000000
    | 9 => 1668106711214627 / 4000000000000
    | 10 => 963081858756683 / 4000000000000
    | 11 => 1709005658835847 / 4000000000000
    | 12 => 1596774772867843 / 4000000000000
    | 13 => 1139533822812019 / 4000000000000
    | 14 => 1292109902446101 / 4000000000000
    | 15 => 1077226527430469 / 4000000000000
    | 16 => 951762305987849 / 4000000000000
    | 17 => 275857812993051 / 800000000000
    | 18 => 763037228340097 / 4000000000000
    | 19 => 646835108869817 / 4000000000000
    | 20 => 404759377613651 / 4000000000000
    | 21 => 217680939449517 / 4000000000000
    | 22 => 591046095579551 / 4000000000000
    | 23 => 807022913428927 / 4000000000000
    | 24 => 341240622386349 / 4000000000000
    | 25 => 1387124184887629 / 4000000000000
    | _ => 926534670533411 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))
    | 1 => (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))
    | 2 => (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000))
    | 3 => (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))
    | 4 => (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))
    | 5 => (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000))
    | 6 => (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))
    | 7 => (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))
    | 8 => (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000))
    | 9 => (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))
    | 10 => (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))
    | 11 => (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000))
    | 12 => (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))
    | 13 => (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))
    | 14 => (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000))
    | 15 => (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))
    | 16 => (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))
    | 17 => (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000))
    | 18 => (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))
    | 19 => (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))
    | 20 => (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000))
    | 21 => (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))
    | 22 => (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))
    | 23 => (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000))
    | 24 => (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))
    | 25 => (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))
    | _ => (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-21258389336 / 1000000000000) (-21258387234 / 1000000000000)
      | 1 => orderedInterval (5587511841 / 1000000000000) (5587511868 / 1000000000000)
      | 2 => orderedInterval (1788987172 / 1000000000000) (1788989772 / 1000000000000)
      | 3 => orderedInterval (5016352435 / 1000000000000) (5016352537 / 1000000000000)
      | 4 => orderedInterval (1616490755 / 1000000000000) (1616490782 / 1000000000000)
      | 5 => orderedInterval (92762759 / 1000000000000) (92762778 / 1000000000000)
      | 6 => orderedInterval (4415456741 / 1000000000000) (4415463127 / 1000000000000)
      | 7 => orderedInterval (-1181859189 / 1000000000000) (-1181859154 / 1000000000000)
      | _ => orderedInterval (-3098787065 / 1000000000000) (-3098785274 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4978908991 / 1000000000000) (4978911095 / 1000000000000)
      | 1 => orderedInterval (3063906731 / 1000000000000) (3063906760 / 1000000000000)
      | 2 => orderedInterval (-2829888715 / 1000000000000) (-2829883815 / 1000000000000)
      | 3 => orderedInterval (19820050941 / 1000000000000) (19820051131 / 1000000000000)
      | 4 => orderedInterval (-5455959636 / 1000000000000) (-5455959593 / 1000000000000)
      | 5 => orderedInterval (-933596740 / 1000000000000) (-933596713 / 1000000000000)
      | 6 => orderedInterval (7586632955 / 1000000000000) (7586638496 / 1000000000000)
      | 7 => orderedInterval (185485316 / 1000000000000) (185485341 / 1000000000000)
      | _ => orderedInterval (-9612337482 / 1000000000000) (-9612334175 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21018823532 / 1000000000000) (21018825649 / 1000000000000)
      | 1 => orderedInterval (-7710967173 / 1000000000000) (-7710967136 / 1000000000000)
      | 2 => orderedInterval (-5601911385 / 1000000000000) (-5601902020 / 1000000000000)
      | 3 => orderedInterval (-21823455613 / 1000000000000) (-21823455237 / 1000000000000)
      | 4 => orderedInterval (-5137275731 / 1000000000000) (-5137275661 / 1000000000000)
      | 5 => orderedInterval (-187328088 / 1000000000000) (-187328048 / 1000000000000)
      | 6 => orderedInterval (-1935938992 / 1000000000000) (-1935934155 / 1000000000000)
      | 7 => orderedInterval (4122899044 / 1000000000000) (4122899067 / 1000000000000)
      | _ => orderedInterval (10266097642 / 1000000000000) (10266103779 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3328788049 / 1000000000000) (-3328785928 / 1000000000000)
      | 1 => orderedInterval (-7054097751 / 1000000000000) (-7054097696 / 1000000000000)
      | 2 => orderedInterval (8816834685 / 1000000000000) (8816852693 / 1000000000000)
      | 3 => orderedInterval (-116626095330 / 1000000000000) (-116626094546 / 1000000000000)
      | 4 => orderedInterval (10624403987 / 1000000000000) (10624404103 / 1000000000000)
      | 5 => orderedInterval (-2489435762 / 1000000000000) (-2489435702 / 1000000000000)
      | 6 => orderedInterval (-8384558938 / 1000000000000) (-8384554739 / 1000000000000)
      | 7 => orderedInterval (14405116 / 1000000000000) (14405139 / 1000000000000)
      | _ => orderedInterval (9599320590 / 1000000000000) (9599331965 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20725184658 / 1000000000000) (-20725182523 / 1000000000000)
      | 1 => orderedInterval (16997886163 / 1000000000000) (16997886247 / 1000000000000)
      | 2 => orderedInterval (18950162529 / 1000000000000) (18950197494 / 1000000000000)
      | 3 => orderedInterval (107658394922 / 1000000000000) (107658396604 / 1000000000000)
      | 4 => orderedInterval (18277445650 / 1000000000000) (18277445850 / 1000000000000)
      | 5 => orderedInterval (510293021 / 1000000000000) (510293117 / 1000000000000)
      | 6 => orderedInterval (905373779 / 1000000000000) (905377447 / 1000000000000)
      | 7 => orderedInterval (-5400547162 / 1000000000000) (-5400547138 / 1000000000000)
      | _ => orderedInterval (-36803401847 / 1000000000000) (-36803380680 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7021473887 / 1000000000000) (-7021460798 / 1000000000000)
    | 1 => orderedInterval (16803202361 / 1000000000000) (16803218527 / 1000000000000)
    | 2 => orderedInterval (-6989056764 / 1000000000000) (-6989033762 / 1000000000000)
    | 3 => orderedInterval (-108828011452 / 1000000000000) (-108827974711 / 1000000000000)
    | _ => orderedInterval (100370422397 / 1000000000000) (100370486418 / 1000000000000)

theorem compactCertificate313_stateChecks0 :
    compactCertificate313.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (373 / 2)) (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (549500223567073 / 4000000000000)) (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (177697082107009 / 800000000000)) (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks1 :
    compactCertificate313.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (160342794763811 / 4000000000000)) (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (430703300815367 / 4000000000000)) (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1169443245437739 / 4000000000000)) (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks2 :
    compactCertificate313.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (861406601631107 / 4000000000000)) (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1476034894100111 / 4000000000000)) (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1087240622386349 / 4000000000000)) (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks3 :
    compactCertificate313.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1668106711214627 / 4000000000000)) (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (963081858756683 / 4000000000000)) (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1709005658835847 / 4000000000000)) (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks4 :
    compactCertificate313.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1596774772867843 / 4000000000000)) (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139533822812019 / 4000000000000)) (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1292109902446101 / 4000000000000)) (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks5 :
    compactCertificate313.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1077226527430469 / 4000000000000)) (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (951762305987849 / 4000000000000)) (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (275857812993051 / 800000000000)) (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks6 :
    compactCertificate313.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (763037228340097 / 4000000000000)) (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (646835108869817 / 4000000000000)) (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (404759377613651 / 4000000000000)) (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks7 :
    compactCertificate313.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (217680939449517 / 4000000000000)) (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (591046095579551 / 4000000000000)) (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (807022913428927 / 4000000000000)) (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_stateChecks8 :
    compactCertificate313.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (341240622386349 / 4000000000000)) (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1387124184887629 / 4000000000000)) (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (926534670533411 / 4000000000000)) (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_states : ∀ j,
    BesselStateValid (compactCertificate313.point j) (compactCertificate313.state j) :=
  compactCertificate313.statesValid_of_checks3 compactCertificate313_stateChecks0
    compactCertificate313_stateChecks1 compactCertificate313_stateChecks2
    compactCertificate313_stateChecks3 compactCertificate313_stateChecks4
    compactCertificate313_stateChecks5 compactCertificate313_stateChecks6
    compactCertificate313_stateChecks7 compactCertificate313_stateChecks8

theorem compactCertificate313_chunkChecks0_0 :
    compactCertificate313.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (373 / 2) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (549500223567073 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (177697082107009 / 800000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000)))) (orderedInterval (-21258389336 / 1000000000000) (-21258387234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (160342794763811 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (430703300815367 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1169443245437739 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000)))) (orderedInterval (5587511841 / 1000000000000) (5587511868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (861406601631107 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1476034894100111 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1087240622386349 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000)))) (orderedInterval (1788987172 / 1000000000000) (1788989772 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks0_1 :
    compactCertificate313.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1668106711214627 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (963081858756683 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1709005658835847 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000)))) (orderedInterval (5016352435 / 1000000000000) (5016352537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1596774772867843 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1139533822812019 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1292109902446101 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000)))) (orderedInterval (1616490755 / 1000000000000) (1616490782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1077226527430469 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (951762305987849 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (275857812993051 / 800000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000)))) (orderedInterval (92762759 / 1000000000000) (92762778 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks0_2 :
    compactCertificate313.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (763037228340097 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (646835108869817 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (404759377613651 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000)))) (orderedInterval (4415456741 / 1000000000000) (4415463127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (217680939449517 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (591046095579551 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (807022913428927 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000)))) (orderedInterval (-1181859189 / 1000000000000) (-1181859154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (341240622386349 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1387124184887629 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (926534670533411 / 4000000000000) 0 (IntervalRat.scale (373 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000)))) (orderedInterval (-3098787065 / 1000000000000) (-3098785274 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks0 :
    compactCertificate313.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate313.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate313_chunkChecks0_0
    compactCertificate313_chunkChecks0_1 compactCertificate313_chunkChecks0_2

theorem compactCertificate313_chunkChecks1_0 :
    compactCertificate313.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (373 / 2) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (549500223567073 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (177697082107009 / 800000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000)))) (orderedInterval (4978908991 / 1000000000000) (4978911095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (160342794763811 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (430703300815367 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1169443245437739 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000)))) (orderedInterval (3063906731 / 1000000000000) (3063906760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (861406601631107 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1476034894100111 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1087240622386349 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000)))) (orderedInterval (-2829888715 / 1000000000000) (-2829883815 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks1_1 :
    compactCertificate313.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1668106711214627 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (963081858756683 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1709005658835847 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000)))) (orderedInterval (19820050941 / 1000000000000) (19820051131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1596774772867843 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1139533822812019 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1292109902446101 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000)))) (orderedInterval (-5455959636 / 1000000000000) (-5455959593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1077226527430469 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (951762305987849 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (275857812993051 / 800000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000)))) (orderedInterval (-933596740 / 1000000000000) (-933596713 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks1_2 :
    compactCertificate313.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (763037228340097 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (646835108869817 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (404759377613651 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000)))) (orderedInterval (7586632955 / 1000000000000) (7586638496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (217680939449517 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (591046095579551 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (807022913428927 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000)))) (orderedInterval (185485316 / 1000000000000) (185485341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (341240622386349 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1387124184887629 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (926534670533411 / 4000000000000) 1 (IntervalRat.scale (373 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000)))) (orderedInterval (-9612337482 / 1000000000000) (-9612334175 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks1 :
    compactCertificate313.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate313.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate313_chunkChecks1_0
    compactCertificate313_chunkChecks1_1 compactCertificate313_chunkChecks1_2

theorem compactCertificate313_chunkChecks2_0 :
    compactCertificate313.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (373 / 2) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (549500223567073 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (177697082107009 / 800000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000)))) (orderedInterval (21018823532 / 1000000000000) (21018825649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (160342794763811 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (430703300815367 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1169443245437739 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000)))) (orderedInterval (-7710967173 / 1000000000000) (-7710967136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (861406601631107 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1476034894100111 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1087240622386349 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000)))) (orderedInterval (-5601911385 / 1000000000000) (-5601902020 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks2_1 :
    compactCertificate313.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1668106711214627 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (963081858756683 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1709005658835847 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000)))) (orderedInterval (-21823455613 / 1000000000000) (-21823455237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1596774772867843 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1139533822812019 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1292109902446101 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000)))) (orderedInterval (-5137275731 / 1000000000000) (-5137275661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1077226527430469 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (951762305987849 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (275857812993051 / 800000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000)))) (orderedInterval (-187328088 / 1000000000000) (-187328048 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks2_2 :
    compactCertificate313.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (763037228340097 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (646835108869817 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (404759377613651 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000)))) (orderedInterval (-1935938992 / 1000000000000) (-1935934155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (217680939449517 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (591046095579551 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (807022913428927 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000)))) (orderedInterval (4122899044 / 1000000000000) (4122899067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (341240622386349 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1387124184887629 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (926534670533411 / 4000000000000) 2 (IntervalRat.scale (373 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000)))) (orderedInterval (10266097642 / 1000000000000) (10266103779 / 1000000000000))) = true
  rfl'

theorem compactCertificate313_chunkChecks2 :
    compactCertificate313.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate313.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate313_chunkChecks2_0
    compactCertificate313_chunkChecks2_1 compactCertificate313_chunkChecks2_2

theorem compactCertificate313_chunkChecks3_0 :
    compactCertificate313.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (373 / 2) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (549500223567073 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (177697082107009 / 800000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000)))) (orderedInterval (-3328788049 / 1000000000000) (-3328785928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (160342794763811 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (430703300815367 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1169443245437739 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000)))) (orderedInterval (-7054097751 / 1000000000000) (-7054097696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (861406601631107 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1476034894100111 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1087240622386349 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000)))) (orderedInterval (8816834685 / 1000000000000) (8816852693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate313_chunkChecks3_1 :
    compactCertificate313.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1668106711214627 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (963081858756683 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1709005658835847 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000)))) (orderedInterval (-116626095330 / 1000000000000) (-116626094546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1596774772867843 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1139533822812019 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1292109902446101 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000)))) (orderedInterval (10624403987 / 1000000000000) (10624404103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1077226527430469 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (951762305987849 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (275857812993051 / 800000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000)))) (orderedInterval (-2489435762 / 1000000000000) (-2489435702 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate313_chunkChecks3_2 :
    compactCertificate313.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (763037228340097 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (646835108869817 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (404759377613651 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000)))) (orderedInterval (-8384558938 / 1000000000000) (-8384554739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (217680939449517 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (591046095579551 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (807022913428927 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000)))) (orderedInterval (14405116 / 1000000000000) (14405139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (341240622386349 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1387124184887629 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (926534670533411 / 4000000000000) 3 (IntervalRat.scale (373 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000)))) (orderedInterval (9599320590 / 1000000000000) (9599331965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate313_chunkChecks3 :
    compactCertificate313.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate313.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate313_chunkChecks3_0
    compactCertificate313_chunkChecks3_1 compactCertificate313_chunkChecks3_2

theorem compactCertificate313_chunkChecks4_0 :
    compactCertificate313.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (373 / 2) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54680637663 / 1000000000000) (-54680632399 / 1000000000000), orderedInterval (20726431807 / 1000000000000) (20726437071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (549500223567073 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4797493519 / 1000000000000) (-4797493505 / 1000000000000), orderedInterval (67923185598 / 1000000000000) (67923185613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (177697082107009 / 800000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7835644768 / 1000000000000) (7835644793 / 1000000000000), orderedInterval (-52977052330 / 1000000000000) (-52977052306 / 1000000000000)))) (orderedInterval (-20725184658 / 1000000000000) (-20725182523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (160342794763811 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3436688121 / 1000000000000) (-3436688115 / 1000000000000), orderedInterval (-125936861933 / 1000000000000) (-125936861926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (430703300815367 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (76674725209 / 1000000000000) (76674725312 / 1000000000000), orderedInterval (-6126452872 / 1000000000000) (-6126452769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1169443245437739 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38693374921 / 1000000000000) (-38693374919 / 1000000000000), orderedInterval (-26017069574 / 1000000000000) (-26017069573 / 1000000000000)))) (orderedInterval (16997886163 / 1000000000000) (16997886247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (861406601631107 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32182521621 / 1000000000000) (32182532194 / 1000000000000), orderedInterval (-43897943621 / 1000000000000) (-43897933048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1476034894100111 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32898139711 / 1000000000000) (-32898070810 / 1000000000000), orderedInterval (25400610102 / 1000000000000) (25400679003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1087240622386349 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32037329666 / 1000000000000) (32037348875 / 1000000000000), orderedInterval (-36332320380 / 1000000000000) (-36332301171 / 1000000000000)))) (orderedInterval (18950162529 / 1000000000000) (18950197494 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate313_chunkChecks4_1 :
    compactCertificate313.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1668106711214627 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (783198414 / 1000000000000) (783198415 / 1000000000000), orderedInterval (-39064427789 / 1000000000000) (-39064427787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (963081858756683 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17501109711 / 1000000000000) (17501110076 / 1000000000000), orderedInterval (-48387245355 / 1000000000000) (-48387244991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1709005658835847 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27145052569 / 1000000000000) (27145052570 / 1000000000000), orderedInterval (27412387635 / 1000000000000) (27412387636 / 1000000000000)))) (orderedInterval (107658394922 / 1000000000000) (107658396604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1596774772867843 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33528227739 / 1000000000000) (-33528227738 / 1000000000000), orderedInterval (-21651818437 / 1000000000000) (-21651818436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1139533822812019 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10155430011 / 1000000000000) (10155430055 / 1000000000000), orderedInterval (-46186403686 / 1000000000000) (-46186403642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1292109902446101 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10053444608 / 1000000000000) (-10053444607 / 1000000000000), orderedInterval (-43224718294 / 1000000000000) (-43224718293 / 1000000000000)))) (orderedInterval (18277445650 / 1000000000000) (18277445850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1077226527430469 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4147227660 / 1000000000000) (-4147227653 / 1000000000000), orderedInterval (48450719400 / 1000000000000) (48450719406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (951762305987849 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1840646030 / 1000000000000) (-1840646026 / 1000000000000), orderedInterval (51696797084 / 1000000000000) (51696797088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (275857812993051 / 800000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1379456258 / 1000000000000) (1379456260 / 1000000000000), orderedInterval (42943603268 / 1000000000000) (42943603269 / 1000000000000)))) (orderedInterval (510293021 / 1000000000000) (510293117 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate313_chunkChecks4_2 :
    compactCertificate313.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (763037228340097 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5370656074 / 1000000000000) (5370656087 / 1000000000000), orderedInterval (-57533297196 / 1000000000000) (-57533297182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (646835108869817 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47933458226 / 1000000000000) (-47933346270 / 1000000000000), orderedInterval (40635361635 / 1000000000000) (40635473592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (404759377613651 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (78671094195 / 1000000000000) (78671094200 / 1000000000000), orderedInterval (9716980676 / 1000000000000) (9716980681 / 1000000000000)))) (orderedInterval (905373779 / 1000000000000) (905377447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (217680939449517 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-105418617465 / 1000000000000) (-105418616928 / 1000000000000), orderedInterval (25148822666 / 1000000000000) (25148823204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (591046095579551 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51056186459 / 1000000000000) (-51056186458 / 1000000000000), orderedInterval (-41078756067 / 1000000000000) (-41078756066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (807022913428927 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55934161446 / 1000000000000) (55934161464 / 1000000000000), orderedInterval (5034273569 / 1000000000000) (5034273586 / 1000000000000)))) (orderedInterval (-5400547162 / 1000000000000) (-5400547138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (341240622386349 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-82533708213 / 1000000000000) (-82533708212 / 1000000000000), orderedInterval (-25021113569 / 1000000000000) (-25021113568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1387124184887629 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39120694441 / 1000000000000) (39120715795 / 1000000000000), orderedInterval (-17531157959 / 1000000000000) (-17531136606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (926534670533411 / 4000000000000) 4 (IntervalRat.scale (373 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3108563691 / 1000000000000) (-3108563685 / 1000000000000), orderedInterval (52339622190 / 1000000000000) (52339622196 / 1000000000000)))) (orderedInterval (-36803401847 / 1000000000000) (-36803380680 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate313_chunkChecks4 :
    compactCertificate313.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate313.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate313_chunkChecks4_0
    compactCertificate313_chunkChecks4_1 compactCertificate313_chunkChecks4_2

theorem compactCertificate313_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate313.chunkCheck r b = true :=
  compactCertificate313.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate313_chunkChecks0
    · exact compactCertificate313_chunkChecks1
    · exact compactCertificate313_chunkChecks2
    · exact compactCertificate313_chunkChecks3
    · exact compactCertificate313_chunkChecks4)

theorem compactCertificate313_coefficient0 :
    compactCertificate313.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate313_coefficient1 :
    compactCertificate313.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate313_coefficient2 :
    compactCertificate313.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate313_coefficient3 :
    compactCertificate313.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate313_coefficient4 :
    compactCertificate313.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate313_coefficients : ∀ r : Fin 5,
    compactCertificate313.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate313_coefficient0
  · exact compactCertificate313_coefficient1
  · exact compactCertificate313_coefficient2
  · exact compactCertificate313_coefficient3
  · exact compactCertificate313_coefficient4

theorem compactCertificate313_lower : (1 : ℚ) ≤ compactCertificate313.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate313, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate313_proves {t : ℝ} (ht : t ∈ compactCertificate313.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate313.proves compactCertificate313_states compactCertificate313_chunks
    compactCertificate313_coefficients compactCertificate313_lower ht

end Erdos232
