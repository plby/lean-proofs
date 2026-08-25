/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate285 : CompactCertificate where
  left := 159
  right := 160
  center := 319 / 2
  grid := fun i =>
    match i.val with
    | 0 => 51
    | 1 => 37
    | 2 => 60
    | 3 => 11
    | 4 => 29
    | 5 => 80
    | 6 => 59
    | 7 => 101
    | 8 => 74
    | 9 => 114
    | 10 => 66
    | 11 => 116
    | 12 => 109
    | 13 => 78
    | 14 => 88
    | 15 => 73
    | 16 => 65
    | 17 => 94
    | 18 => 52
    | 19 => 44
    | 20 => 28
    | 21 => 15
    | 22 => 40
    | 23 => 55
    | 24 => 23
    | 25 => 94
    | _ => 63
  point := fun i =>
    match i.val with
    | 0 => 319 / 2
    | 1 => 469947912380419 / 4000000000000
    | 2 => 151971499174627 / 800000000000
    | 3 => 137129628765833 / 4000000000000
    | 4 => 368349471742901 / 4000000000000
    | 5 => 1000140469958817 / 4000000000000
    | 6 => 736698943486121 / 4000000000000
    | 7 => 1262346196294733 / 4000000000000
    | 8 => 929838494748647 / 4000000000000
    | 9 => 1426611369644681 / 4000000000000
    | 10 => 823654458293249 / 4000000000000
    | 11 => 1461589289996341 / 4000000000000
    | 12 => 1365606307090729 / 4000000000000
    | 13 => 974561097793657 / 4000000000000
    | 14 => 1105048415228703 / 4000000000000
    | 15 => 921274161529007 / 4000000000000
    | 16 => 813973661153147 / 4000000000000
    | 17 => 235921293149553 / 800000000000
    | 18 => 652570712709091 / 4000000000000
    | 19 => 553191420186251 / 4000000000000
    | 20 => 346161505251353 / 4000000000000
    | 21 => 186166808805351 / 4000000000000
    | 22 => 505479100509053 / 4000000000000
    | 23 => 690188497007581 / 4000000000000
    | 24 => 291838494748647 / 4000000000000
    | 25 => 1186307278764487 / 4000000000000
    | _ => 792398283914633 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))
    | 1 => (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))
    | 2 => (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000))
    | 3 => (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))
    | 4 => (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))
    | 5 => (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000))
    | 6 => (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))
    | 7 => (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))
    | 8 => (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000))
    | 9 => (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))
    | 10 => (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))
    | 11 => (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000))
    | 12 => (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))
    | 13 => (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))
    | 14 => (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
    | 15 => (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))
    | 16 => (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))
    | 17 => (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000))
    | 18 => (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))
    | 19 => (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))
    | 20 => (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000))
    | 21 => (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))
    | 22 => (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))
    | 23 => (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000))
    | 24 => (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))
    | 25 => (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))
    | _ => (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (435144092 / 1000000000000) (435150536 / 1000000000000)
      | 1 => orderedInterval (-518215720 / 1000000000000) (-518215517 / 1000000000000)
      | 2 => orderedInterval (-232555446 / 1000000000000) (-232552397 / 1000000000000)
      | 3 => orderedInterval (8205289608 / 1000000000000) (8205292769 / 1000000000000)
      | 4 => orderedInterval (-3130043703 / 1000000000000) (-3130042932 / 1000000000000)
      | 5 => orderedInterval (81163117 / 1000000000000) (81163145 / 1000000000000)
      | 6 => orderedInterval (-9902367782 / 1000000000000) (-9902367055 / 1000000000000)
      | 7 => orderedInterval (1235233198 / 1000000000000) (1235233218 / 1000000000000)
      | _ => orderedInterval (4833431804 / 1000000000000) (4833434273 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-27320007699 / 1000000000000) (-27320000070 / 1000000000000)
      | 1 => orderedInterval (-4296656501 / 1000000000000) (-4296656208 / 1000000000000)
      | 2 => orderedInterval (2968554389 / 1000000000000) (2968560419 / 1000000000000)
      | 3 => orderedInterval (-11105340248 / 1000000000000) (-11105334057 / 1000000000000)
      | 4 => orderedInterval (7290906520 / 1000000000000) (7290907698 / 1000000000000)
      | 5 => orderedInterval (6288220644 / 1000000000000) (6288220686 / 1000000000000)
      | 6 => orderedInterval (-9577189477 / 1000000000000) (-9577189067 / 1000000000000)
      | 7 => orderedInterval (4819800756 / 1000000000000) (4819800775 / 1000000000000)
      | _ => orderedInterval (10742596323 / 1000000000000) (10742600893 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1647708526 / 1000000000000) (-1647699425 / 1000000000000)
      | 1 => orderedInterval (-3296620140 / 1000000000000) (-3296619693 / 1000000000000)
      | 2 => orderedInterval (2462965121 / 1000000000000) (2462977086 / 1000000000000)
      | 3 => orderedInterval (-50678494476 / 1000000000000) (-50678481711 / 1000000000000)
      | 4 => orderedInterval (7775904193 / 1000000000000) (7775906006 / 1000000000000)
      | 5 => orderedInterval (-683167818 / 1000000000000) (-683167758 / 1000000000000)
      | 6 => orderedInterval (8314789334 / 1000000000000) (8314789575 / 1000000000000)
      | 7 => orderedInterval (-1879889833 / 1000000000000) (-1879889815 / 1000000000000)
      | _ => orderedInterval (-1870111527 / 1000000000000) (-1870103026 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (28504775364 / 1000000000000) (28504786178 / 1000000000000)
      | 1 => orderedInterval (11982922346 / 1000000000000) (11982923038 / 1000000000000)
      | 2 => orderedInterval (-9264245096 / 1000000000000) (-9264221428 / 1000000000000)
      | 3 => orderedInterval (70649683899 / 1000000000000) (70649711034 / 1000000000000)
      | 4 => orderedInterval (-20466216455 / 1000000000000) (-20466213676 / 1000000000000)
      | 5 => orderedInterval (-13969901463 / 1000000000000) (-13969901373 / 1000000000000)
      | 6 => orderedInterval (10241883290 / 1000000000000) (10241883436 / 1000000000000)
      | 7 => orderedInterval (-5012731576 / 1000000000000) (-5012731558 / 1000000000000)
      | _ => orderedInterval (-22821911368 / 1000000000000) (-22821895592 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (3178389904 / 1000000000000) (3178402832 / 1000000000000)
      | 1 => orderedInterval (10046031895 / 1000000000000) (10046032978 / 1000000000000)
      | 2 => orderedInterval (-12936104423 / 1000000000000) (-12936057453 / 1000000000000)
      | 3 => orderedInterval (274237993319 / 1000000000000) (274238052439 / 1000000000000)
      | 4 => orderedInterval (-20225726389 / 1000000000000) (-20225722105 / 1000000000000)
      | 5 => orderedInterval (3335146475 / 1000000000000) (3335146611 / 1000000000000)
      | 6 => orderedInterval (-7755212122 / 1000000000000) (-7755212027 / 1000000000000)
      | 7 => orderedInterval (2734345550 / 1000000000000) (2734345569 / 1000000000000)
      | _ => orderedInterval (-18908598709 / 1000000000000) (-18908569313 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1007079168 / 1000000000000) (1007096040 / 1000000000000)
    | 1 => orderedInterval (-20189115293 / 1000000000000) (-20189088931 / 1000000000000)
    | 2 => orderedInterval (-41502333672 / 1000000000000) (-41502288761 / 1000000000000)
    | 3 => orderedInterval (49844258941 / 1000000000000) (49844340059 / 1000000000000)
    | _ => orderedInterval (233706265500 / 1000000000000) (233706419531 / 1000000000000)

theorem compactCertificate285_stateChecks0 :
    compactCertificate285.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (319 / 2)) (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (469947912380419 / 4000000000000)) (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (151971499174627 / 800000000000)) (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks1 :
    compactCertificate285.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (137129628765833 / 4000000000000)) (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (368349471742901 / 4000000000000)) (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1000140469958817 / 4000000000000)) (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks2 :
    compactCertificate285.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (736698943486121 / 4000000000000)) (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1262346196294733 / 4000000000000)) (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (929838494748647 / 4000000000000)) (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks3 :
    compactCertificate285.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1426611369644681 / 4000000000000)) (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (823654458293249 / 4000000000000)) (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1461589289996341 / 4000000000000)) (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks4 :
    compactCertificate285.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1365606307090729 / 4000000000000)) (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (974561097793657 / 4000000000000)) (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1105048415228703 / 4000000000000)) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks5 :
    compactCertificate285.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (921274161529007 / 4000000000000)) (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (813973661153147 / 4000000000000)) (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (235921293149553 / 800000000000)) (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks6 :
    compactCertificate285.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (652570712709091 / 4000000000000)) (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (553191420186251 / 4000000000000)) (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (346161505251353 / 4000000000000)) (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks7 :
    compactCertificate285.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (186166808805351 / 4000000000000)) (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (505479100509053 / 4000000000000)) (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (690188497007581 / 4000000000000)) (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_stateChecks8 :
    compactCertificate285.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (291838494748647 / 4000000000000)) (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1186307278764487 / 4000000000000)) (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (792398283914633 / 4000000000000)) (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_states : ∀ j,
    BesselStateValid (compactCertificate285.point j) (compactCertificate285.state j) :=
  compactCertificate285.statesValid_of_checks3 compactCertificate285_stateChecks0
    compactCertificate285_stateChecks1 compactCertificate285_stateChecks2
    compactCertificate285_stateChecks3 compactCertificate285_stateChecks4
    compactCertificate285_stateChecks5 compactCertificate285_stateChecks6
    compactCertificate285_stateChecks7 compactCertificate285_stateChecks8

theorem compactCertificate285_chunkChecks0_0 :
    compactCertificate285.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (319 / 2) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (469947912380419 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (151971499174627 / 800000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000)))) (orderedInterval (435144092 / 1000000000000) (435150536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (137129628765833 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (368349471742901 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1000140469958817 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000)))) (orderedInterval (-518215720 / 1000000000000) (-518215517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (736698943486121 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1262346196294733 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (929838494748647 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000)))) (orderedInterval (-232555446 / 1000000000000) (-232552397 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks0_1 :
    compactCertificate285.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1426611369644681 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (823654458293249 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1461589289996341 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000)))) (orderedInterval (8205289608 / 1000000000000) (8205292769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1365606307090729 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (974561097793657 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000)))) (orderedInterval (-3130043703 / 1000000000000) (-3130042932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (921274161529007 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (813973661153147 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (235921293149553 / 800000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000)))) (orderedInterval (81163117 / 1000000000000) (81163145 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks0_2 :
    compactCertificate285.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (652570712709091 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (553191420186251 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (346161505251353 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000)))) (orderedInterval (-9902367782 / 1000000000000) (-9902367055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (186166808805351 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (505479100509053 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (690188497007581 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000)))) (orderedInterval (1235233198 / 1000000000000) (1235233218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (291838494748647 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1186307278764487 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (792398283914633 / 4000000000000) 0 (IntervalRat.scale (319 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000)))) (orderedInterval (4833431804 / 1000000000000) (4833434273 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks0 :
    compactCertificate285.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate285.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate285_chunkChecks0_0
    compactCertificate285_chunkChecks0_1 compactCertificate285_chunkChecks0_2

theorem compactCertificate285_chunkChecks1_0 :
    compactCertificate285.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (319 / 2) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (469947912380419 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (151971499174627 / 800000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000)))) (orderedInterval (-27320007699 / 1000000000000) (-27320000070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (137129628765833 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (368349471742901 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1000140469958817 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000)))) (orderedInterval (-4296656501 / 1000000000000) (-4296656208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (736698943486121 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1262346196294733 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (929838494748647 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000)))) (orderedInterval (2968554389 / 1000000000000) (2968560419 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks1_1 :
    compactCertificate285.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1426611369644681 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (823654458293249 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1461589289996341 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000)))) (orderedInterval (-11105340248 / 1000000000000) (-11105334057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1365606307090729 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (974561097793657 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000)))) (orderedInterval (7290906520 / 1000000000000) (7290907698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (921274161529007 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (813973661153147 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (235921293149553 / 800000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000)))) (orderedInterval (6288220644 / 1000000000000) (6288220686 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks1_2 :
    compactCertificate285.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (652570712709091 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (553191420186251 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (346161505251353 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000)))) (orderedInterval (-9577189477 / 1000000000000) (-9577189067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (186166808805351 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (505479100509053 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (690188497007581 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000)))) (orderedInterval (4819800756 / 1000000000000) (4819800775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (291838494748647 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1186307278764487 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (792398283914633 / 4000000000000) 1 (IntervalRat.scale (319 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000)))) (orderedInterval (10742596323 / 1000000000000) (10742600893 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks1 :
    compactCertificate285.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate285.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate285_chunkChecks1_0
    compactCertificate285_chunkChecks1_1 compactCertificate285_chunkChecks1_2

theorem compactCertificate285_chunkChecks2_0 :
    compactCertificate285.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (319 / 2) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (469947912380419 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (151971499174627 / 800000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000)))) (orderedInterval (-1647708526 / 1000000000000) (-1647699425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (137129628765833 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (368349471742901 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1000140469958817 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000)))) (orderedInterval (-3296620140 / 1000000000000) (-3296619693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (736698943486121 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1262346196294733 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (929838494748647 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000)))) (orderedInterval (2462965121 / 1000000000000) (2462977086 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks2_1 :
    compactCertificate285.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1426611369644681 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (823654458293249 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1461589289996341 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000)))) (orderedInterval (-50678494476 / 1000000000000) (-50678481711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1365606307090729 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (974561097793657 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000)))) (orderedInterval (7775904193 / 1000000000000) (7775906006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (921274161529007 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (813973661153147 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (235921293149553 / 800000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000)))) (orderedInterval (-683167818 / 1000000000000) (-683167758 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks2_2 :
    compactCertificate285.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (652570712709091 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (553191420186251 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (346161505251353 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000)))) (orderedInterval (8314789334 / 1000000000000) (8314789575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (186166808805351 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (505479100509053 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (690188497007581 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000)))) (orderedInterval (-1879889833 / 1000000000000) (-1879889815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (291838494748647 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1186307278764487 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (792398283914633 / 4000000000000) 2 (IntervalRat.scale (319 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000)))) (orderedInterval (-1870111527 / 1000000000000) (-1870103026 / 1000000000000))) = true
  rfl'

theorem compactCertificate285_chunkChecks2 :
    compactCertificate285.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate285.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate285_chunkChecks2_0
    compactCertificate285_chunkChecks2_1 compactCertificate285_chunkChecks2_2

theorem compactCertificate285_chunkChecks3_0 :
    compactCertificate285.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (319 / 2) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (469947912380419 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (151971499174627 / 800000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000)))) (orderedInterval (28504775364 / 1000000000000) (28504786178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (137129628765833 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (368349471742901 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1000140469958817 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000)))) (orderedInterval (11982922346 / 1000000000000) (11982923038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (736698943486121 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1262346196294733 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (929838494748647 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000)))) (orderedInterval (-9264245096 / 1000000000000) (-9264221428 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate285_chunkChecks3_1 :
    compactCertificate285.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1426611369644681 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (823654458293249 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1461589289996341 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000)))) (orderedInterval (70649683899 / 1000000000000) (70649711034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1365606307090729 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (974561097793657 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000)))) (orderedInterval (-20466216455 / 1000000000000) (-20466213676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (921274161529007 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (813973661153147 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (235921293149553 / 800000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000)))) (orderedInterval (-13969901463 / 1000000000000) (-13969901373 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate285_chunkChecks3_2 :
    compactCertificate285.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (652570712709091 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (553191420186251 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (346161505251353 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000)))) (orderedInterval (10241883290 / 1000000000000) (10241883436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (186166808805351 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (505479100509053 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (690188497007581 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000)))) (orderedInterval (-5012731576 / 1000000000000) (-5012731558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (291838494748647 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1186307278764487 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (792398283914633 / 4000000000000) 3 (IntervalRat.scale (319 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000)))) (orderedInterval (-22821911368 / 1000000000000) (-22821895592 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate285_chunkChecks3 :
    compactCertificate285.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate285.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate285_chunkChecks3_0
    compactCertificate285_chunkChecks3_1 compactCertificate285_chunkChecks3_2

theorem compactCertificate285_chunkChecks4_0 :
    compactCertificate285.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (319 / 2) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4002051527 / 1000000000000) (-4002051525 / 1000000000000), orderedInterval (-63037827795 / 1000000000000) (-63037827793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (469947912380419 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65907429972 / 1000000000000) (-65907419542 / 1000000000000), orderedInterval (33064968846 / 1000000000000) (33064979276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (151971499174627 / 800000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44913009699 / 1000000000000) (44913117639 / 1000000000000), orderedInterval (-36643228222 / 1000000000000) (-36643120282 / 1000000000000)))) (orderedInterval (3178389904 / 1000000000000) (3178402832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (137129628765833 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66121247788 / 1000000000000) (-66121247787 / 1000000000000), orderedInterval (-118194947471 / 1000000000000) (-118194947470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (368349471742901 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-81578581214 / 1000000000000) (-81578580756 / 1000000000000), orderedInterval (16507044289 / 1000000000000) (16507044747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1000140469958817 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24518230920 / 1000000000000) (-24518228583 / 1000000000000), orderedInterval (44150961582 / 1000000000000) (44150963919 / 1000000000000)))) (orderedInterval (10046031895 / 1000000000000) (10046032978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (736698943486121 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22597428424 / 1000000000000) (22597429355 / 1000000000000), orderedInterval (-54338163061 / 1000000000000) (-54338162129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1262346196294733 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35985188238 / 1000000000000) (35985286780 / 1000000000000), orderedInterval (-26933086256 / 1000000000000) (-26932987714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (929838494748647 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36303119819 / 1000000000000) (36303119820 / 1000000000000), orderedInterval (37614207647 / 1000000000000) (37614207648 / 1000000000000)))) (orderedInterval (-12936104423 / 1000000000000) (-12936057453 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate285_chunkChecks4_1 :
    compactCertificate285.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1426611369644681 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27336079854 / 1000000000000) (-27336069405 / 1000000000000), orderedInterval (32252037327 / 1000000000000) (32252047776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (823654458293249 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33504245606 / 1000000000000) (-33504232974 / 1000000000000), orderedInterval (44456478041 / 1000000000000) (44456490673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1461589289996341 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (41014051355 / 1000000000000) (41014053502 / 1000000000000), orderedInterval (-7809393025 / 1000000000000) (-7809390878 / 1000000000000)))) (orderedInterval (274237993319 / 1000000000000) (274238052439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1365606307090729 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10557535770 / 1000000000000) (10557535815 / 1000000000000), orderedInterval (-41887461872 / 1000000000000) (-41887461827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (974561097793657 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29661946799 / 1000000000000) (-29661938868 / 1000000000000), orderedInterval (41691633080 / 1000000000000) (41691641010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000)))) (orderedInterval (-20225726389 / 1000000000000) (-20225722105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (921274161529007 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-51564431265 / 1000000000000) (-51564430174 / 1000000000000), orderedInterval (10368030272 / 1000000000000) (10368031363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (813973661153147 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4172973748 / 1000000000000) (-4172973747 / 1000000000000), orderedInterval (-55766529944 / 1000000000000) (-55766529942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (235921293149553 / 800000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17099187423 / 1000000000000) (17099187424 / 1000000000000), orderedInterval (43172549574 / 1000000000000) (43172549575 / 1000000000000)))) (orderedInterval (3335146475 / 1000000000000) (3335146611 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate285_chunkChecks4_2 :
    compactCertificate285.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (652570712709091 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33419376698 / 1000000000000) (33419376699 / 1000000000000), orderedInterval (52674278019 / 1000000000000) (52674278020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (553191420186251 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51073785368 / 1000000000000) (51073785369 / 1000000000000), orderedInterval (44477590926 / 1000000000000) (44477590927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (346161505251353 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51238645995 / 1000000000000) (-51238624925 / 1000000000000), orderedInterval (69078062662 / 1000000000000) (69078083732 / 1000000000000)))) (orderedInterval (-7755212122 / 1000000000000) (-7755212027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (186166808805351 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-23294932200 / 1000000000000) (-23294932199 / 1000000000000), orderedInterval (-114364572649 / 1000000000000) (-114364572648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (505479100509053 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (70748041735 / 1000000000000) (70748041747 / 1000000000000), orderedInterval (5414737906 / 1000000000000) (5414737918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (690188497007581 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31448018726 / 1000000000000) (-31448018725 / 1000000000000), orderedInterval (-51875888301 / 1000000000000) (-51875888300 / 1000000000000)))) (orderedInterval (2734345550 / 1000000000000) (2734345569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (291838494748647 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-93079777079 / 1000000000000) (-93079777072 / 1000000000000), orderedInterval (-7210590852 / 1000000000000) (-7210590844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1186307278764487 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41067650356 / 1000000000000) (41067680131 / 1000000000000), orderedInterval (-21516966516 / 1000000000000) (-21516936741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (792398283914633 / 4000000000000) 4 (IntervalRat.scale (319 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46568731685 / 1000000000000) (-46568731684 / 1000000000000), orderedInterval (-32208688880 / 1000000000000) (-32208688879 / 1000000000000)))) (orderedInterval (-18908598709 / 1000000000000) (-18908569313 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate285_chunkChecks4 :
    compactCertificate285.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate285.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate285_chunkChecks4_0
    compactCertificate285_chunkChecks4_1 compactCertificate285_chunkChecks4_2

theorem compactCertificate285_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate285.chunkCheck r b = true :=
  compactCertificate285.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate285_chunkChecks0
    · exact compactCertificate285_chunkChecks1
    · exact compactCertificate285_chunkChecks2
    · exact compactCertificate285_chunkChecks3
    · exact compactCertificate285_chunkChecks4)

theorem compactCertificate285_coefficient0 :
    compactCertificate285.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate285_coefficient1 :
    compactCertificate285.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate285_coefficient2 :
    compactCertificate285.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate285_coefficient3 :
    compactCertificate285.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate285_coefficient4 :
    compactCertificate285.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate285_coefficients : ∀ r : Fin 5,
    compactCertificate285.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate285_coefficient0
  · exact compactCertificate285_coefficient1
  · exact compactCertificate285_coefficient2
  · exact compactCertificate285_coefficient3
  · exact compactCertificate285_coefficient4

theorem compactCertificate285_lower : (1 : ℚ) ≤ compactCertificate285.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate285, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate285_proves {t : ℝ} (ht : t ∈ compactCertificate285.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate285.proves compactCertificate285_states compactCertificate285_chunks
    compactCertificate285_coefficients compactCertificate285_lower ht

end Erdos232
