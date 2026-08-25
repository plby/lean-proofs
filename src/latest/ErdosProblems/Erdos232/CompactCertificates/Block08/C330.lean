/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate330 : CompactCertificate where
  left := 202
  right := 203
  center := 405 / 2
  grid := fun i =>
    match i.val with
    | 0 => 64
    | 1 => 48
    | 2 => 77
    | 3 => 14
    | 4 => 37
    | 5 => 101
    | 6 => 74
    | 7 => 128
    | 8 => 94
    | 9 => 144
    | 10 => 83
    | 11 => 148
    | 12 => 138
    | 13 => 99
    | 14 => 112
    | 15 => 93
    | 16 => 82
    | 17 => 119
    | 18 => 66
    | 19 => 56
    | 20 => 35
    | 21 => 19
    | 22 => 51
    | 23 => 70
    | 24 => 29
    | 25 => 120
    | _ => 80
  point := fun i =>
    match i.val with
    | 0 => 405 / 2
    | 1 => 119328466779981 / 800000000000
    | 2 => 38588374398573 / 160000000000
    | 3 => 34819748996967 / 800000000000
    | 4 => 93530743608699 / 800000000000
    | 5 => 253954163218383 / 800000000000
    | 6 => 187061487217479 / 800000000000
    | 7 => 320533046708067 / 800000000000
    | 8 => 236103191456553 / 800000000000
    | 9 => 362243012354919 / 800000000000
    | 10 => 209141100695151 / 800000000000
    | 11 => 371124553259259 / 800000000000
    | 12 => 346752698665671 / 800000000000
    | 13 => 247459087527543 / 800000000000
    | 14 => 280592230826097 / 800000000000
    | 15 => 233928548852193 / 800000000000
    | 16 => 206682967252053 / 800000000000
    | 17 => 59904779765247 / 160000000000
    | 18 => 165699773446509 / 800000000000
    | 19 => 140465533025349 / 800000000000
    | 20 => 87896808543447 / 800000000000
    | 21 => 47271195966249 / 800000000000
    | 22 => 128350492605747 / 800000000000
    | 23 => 175251624632019 / 800000000000
    | 24 => 74103191456553 / 800000000000
    | 25 => 301225359184713 / 800000000000
    | _ => 201204579928167 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))
    | 1 => (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))
    | 2 => (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000))
    | 3 => (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))
    | 4 => (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))
    | 5 => (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000))
    | 6 => (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))
    | 7 => (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))
    | 8 => (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000))
    | 9 => (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))
    | 10 => (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))
    | 11 => (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000))
    | 12 => (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))
    | 13 => (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))
    | 14 => (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000))
    | 15 => (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))
    | 16 => (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))
    | 17 => (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000))
    | 18 => (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))
    | 19 => (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))
    | 20 => (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000))
    | 21 => (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))
    | 22 => (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))
    | 23 => (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000))
    | 24 => (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))
    | 25 => (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))
    | _ => (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17027072379 / 1000000000000) (17027108242 / 1000000000000)
      | 1 => orderedInterval (-550236129 / 1000000000000) (-550236104 / 1000000000000)
      | 2 => orderedInterval (1403589317 / 1000000000000) (1403589516 / 1000000000000)
      | 3 => orderedInterval (-11220849339 / 1000000000000) (-11220849252 / 1000000000000)
      | 4 => orderedInterval (3015941646 / 1000000000000) (3015949727 / 1000000000000)
      | 5 => orderedInterval (-4327268503 / 1000000000000) (-4327268480 / 1000000000000)
      | 6 => orderedInterval (-7780854658 / 1000000000000) (-7780854606 / 1000000000000)
      | 7 => orderedInterval (1807144759 / 1000000000000) (1807144785 / 1000000000000)
      | _ => orderedInterval (-9191515889 / 1000000000000) (-9191515156 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16816940064 / 1000000000000) (-16816904453 / 1000000000000)
      | 1 => orderedInterval (2556424987 / 1000000000000) (2556425016 / 1000000000000)
      | 2 => orderedInterval (-560247662 / 1000000000000) (-560247271 / 1000000000000)
      | 3 => orderedInterval (5740191095 / 1000000000000) (5740191272 / 1000000000000)
      | 4 => orderedInterval (-5534097360 / 1000000000000) (-5534085015 / 1000000000000)
      | 5 => orderedInterval (-992229688 / 1000000000000) (-992229654 / 1000000000000)
      | 6 => orderedInterval (-11347191367 / 1000000000000) (-11347191319 / 1000000000000)
      | 7 => orderedInterval (-3304893935 / 1000000000000) (-3304893912 / 1000000000000)
      | _ => orderedInterval (-12413618423 / 1000000000000) (-12413618034 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17078368341 / 1000000000000) (-17078332739 / 1000000000000)
      | 1 => orderedInterval (-5357423655 / 1000000000000) (-5357423616 / 1000000000000)
      | 2 => orderedInterval (-4350059445 / 1000000000000) (-4350058674 / 1000000000000)
      | 3 => orderedInterval (44306540673 / 1000000000000) (44306541053 / 1000000000000)
      | 4 => orderedInterval (-6071337984 / 1000000000000) (-6071319060 / 1000000000000)
      | 5 => orderedInterval (9100166006 / 1000000000000) (9100166055 / 1000000000000)
      | 6 => orderedInterval (6571806919 / 1000000000000) (6571806965 / 1000000000000)
      | 7 => orderedInterval (-1068998503 / 1000000000000) (-1068998480 / 1000000000000)
      | _ => orderedInterval (15796505438 / 1000000000000) (15796505698 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18536310103 / 1000000000000) (18536345567 / 1000000000000)
      | 1 => orderedInterval (-7252812925 / 1000000000000) (-7252812867 / 1000000000000)
      | 2 => orderedInterval (4622731971 / 1000000000000) (4622733490 / 1000000000000)
      | 3 => orderedInterval (-33533967393 / 1000000000000) (-33533966564 / 1000000000000)
      | 4 => orderedInterval (15751483961 / 1000000000000) (15751512878 / 1000000000000)
      | 5 => orderedInterval (2547257767 / 1000000000000) (2547257840 / 1000000000000)
      | 6 => orderedInterval (10281201461 / 1000000000000) (10281201506 / 1000000000000)
      | 7 => orderedInterval (4798362659 / 1000000000000) (4798362683 / 1000000000000)
      | _ => orderedInterval (30562571774 / 1000000000000) (30562572020 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16984952227 / 1000000000000) (16984987766 / 1000000000000)
      | 1 => orderedInterval (15148284954 / 1000000000000) (15148285043 / 1000000000000)
      | 2 => orderedInterval (14569151650 / 1000000000000) (14569154653 / 1000000000000)
      | 3 => orderedInterval (-202952068528 / 1000000000000) (-202952066685 / 1000000000000)
      | 4 => orderedInterval (9700162521 / 1000000000000) (9700206858 / 1000000000000)
      | 5 => orderedInterval (-21561820185 / 1000000000000) (-21561820071 / 1000000000000)
      | 6 => orderedInterval (-6245520499 / 1000000000000) (-6245520455 / 1000000000000)
      | 7 => orderedInterval (780707112 / 1000000000000) (780707137 / 1000000000000)
      | _ => orderedInterval (-31560164844 / 1000000000000) (-31560164523 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9816976417 / 1000000000000) (-9816931328 / 1000000000000)
    | 1 => orderedInterval (-42672602417 / 1000000000000) (-42672553370 / 1000000000000)
    | 2 => orderedInterval (41848831108 / 1000000000000) (41848887202 / 1000000000000)
    | 3 => orderedInterval (46313139378 / 1000000000000) (46313206553 / 1000000000000)
    | _ => orderedInterval (-205136315592 / 1000000000000) (-205136230277 / 1000000000000)

theorem compactCertificate330_stateChecks0 :
    compactCertificate330.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (405 / 2)) (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (119328466779981 / 800000000000)) (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (38588374398573 / 160000000000)) (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks1 :
    compactCertificate330.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (34819748996967 / 800000000000)) (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (93530743608699 / 800000000000)) (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (253954163218383 / 800000000000)) (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks2 :
    compactCertificate330.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (187061487217479 / 800000000000)) (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (320533046708067 / 800000000000)) (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (236103191456553 / 800000000000)) (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks3 :
    compactCertificate330.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (362243012354919 / 800000000000)) (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (209141100695151 / 800000000000)) (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (371124553259259 / 800000000000)) (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks4 :
    compactCertificate330.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (346752698665671 / 800000000000)) (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (247459087527543 / 800000000000)) (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280592230826097 / 800000000000)) (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks5 :
    compactCertificate330.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (233928548852193 / 800000000000)) (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206682967252053 / 800000000000)) (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (59904779765247 / 160000000000)) (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks6 :
    compactCertificate330.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (165699773446509 / 800000000000)) (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (140465533025349 / 800000000000)) (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (87896808543447 / 800000000000)) (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks7 :
    compactCertificate330.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (47271195966249 / 800000000000)) (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128350492605747 / 800000000000)) (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175251624632019 / 800000000000)) (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_stateChecks8 :
    compactCertificate330.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (74103191456553 / 800000000000)) (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (301225359184713 / 800000000000)) (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201204579928167 / 800000000000)) (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_states : ∀ j,
    BesselStateValid (compactCertificate330.point j) (compactCertificate330.state j) :=
  compactCertificate330.statesValid_of_checks3 compactCertificate330_stateChecks0
    compactCertificate330_stateChecks1 compactCertificate330_stateChecks2
    compactCertificate330_stateChecks3 compactCertificate330_stateChecks4
    compactCertificate330_stateChecks5 compactCertificate330_stateChecks6
    compactCertificate330_stateChecks7 compactCertificate330_stateChecks8

theorem compactCertificate330_chunkChecks0_0 :
    compactCertificate330.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (405 / 2) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (119328466779981 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (38588374398573 / 160000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000)))) (orderedInterval (17027072379 / 1000000000000) (17027108242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (34819748996967 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (93530743608699 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (253954163218383 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000)))) (orderedInterval (-550236129 / 1000000000000) (-550236104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (187061487217479 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (320533046708067 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (236103191456553 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000)))) (orderedInterval (1403589317 / 1000000000000) (1403589516 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks0_1 :
    compactCertificate330.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (362243012354919 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (209141100695151 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (371124553259259 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000)))) (orderedInterval (-11220849339 / 1000000000000) (-11220849252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (346752698665671 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (247459087527543 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (280592230826097 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000)))) (orderedInterval (3015941646 / 1000000000000) (3015949727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (233928548852193 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (206682967252053 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (59904779765247 / 160000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000)))) (orderedInterval (-4327268503 / 1000000000000) (-4327268480 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks0_2 :
    compactCertificate330.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (165699773446509 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (140465533025349 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (87896808543447 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000)))) (orderedInterval (-7780854658 / 1000000000000) (-7780854606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (47271195966249 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (128350492605747 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (175251624632019 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000)))) (orderedInterval (1807144759 / 1000000000000) (1807144785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (74103191456553 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (301225359184713 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (201204579928167 / 800000000000) 0 (IntervalRat.scale (405 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000)))) (orderedInterval (-9191515889 / 1000000000000) (-9191515156 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks0 :
    compactCertificate330.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate330.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate330_chunkChecks0_0
    compactCertificate330_chunkChecks0_1 compactCertificate330_chunkChecks0_2

theorem compactCertificate330_chunkChecks1_0 :
    compactCertificate330.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (405 / 2) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (119328466779981 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (38588374398573 / 160000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000)))) (orderedInterval (-16816940064 / 1000000000000) (-16816904453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (34819748996967 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (93530743608699 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (253954163218383 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000)))) (orderedInterval (2556424987 / 1000000000000) (2556425016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (187061487217479 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (320533046708067 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (236103191456553 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000)))) (orderedInterval (-560247662 / 1000000000000) (-560247271 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks1_1 :
    compactCertificate330.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (362243012354919 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (209141100695151 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (371124553259259 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000)))) (orderedInterval (5740191095 / 1000000000000) (5740191272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (346752698665671 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (247459087527543 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (280592230826097 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000)))) (orderedInterval (-5534097360 / 1000000000000) (-5534085015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (233928548852193 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (206682967252053 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (59904779765247 / 160000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000)))) (orderedInterval (-992229688 / 1000000000000) (-992229654 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks1_2 :
    compactCertificate330.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (165699773446509 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (140465533025349 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (87896808543447 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000)))) (orderedInterval (-11347191367 / 1000000000000) (-11347191319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (47271195966249 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (128350492605747 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (175251624632019 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000)))) (orderedInterval (-3304893935 / 1000000000000) (-3304893912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (74103191456553 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (301225359184713 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (201204579928167 / 800000000000) 1 (IntervalRat.scale (405 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000)))) (orderedInterval (-12413618423 / 1000000000000) (-12413618034 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks1 :
    compactCertificate330.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate330.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate330_chunkChecks1_0
    compactCertificate330_chunkChecks1_1 compactCertificate330_chunkChecks1_2

theorem compactCertificate330_chunkChecks2_0 :
    compactCertificate330.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (405 / 2) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (119328466779981 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (38588374398573 / 160000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000)))) (orderedInterval (-17078368341 / 1000000000000) (-17078332739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (34819748996967 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (93530743608699 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (253954163218383 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000)))) (orderedInterval (-5357423655 / 1000000000000) (-5357423616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (187061487217479 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (320533046708067 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (236103191456553 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000)))) (orderedInterval (-4350059445 / 1000000000000) (-4350058674 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks2_1 :
    compactCertificate330.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (362243012354919 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (209141100695151 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (371124553259259 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000)))) (orderedInterval (44306540673 / 1000000000000) (44306541053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (346752698665671 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (247459087527543 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (280592230826097 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000)))) (orderedInterval (-6071337984 / 1000000000000) (-6071319060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (233928548852193 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (206682967252053 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (59904779765247 / 160000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000)))) (orderedInterval (9100166006 / 1000000000000) (9100166055 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks2_2 :
    compactCertificate330.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (165699773446509 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (140465533025349 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (87896808543447 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000)))) (orderedInterval (6571806919 / 1000000000000) (6571806965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (47271195966249 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (128350492605747 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (175251624632019 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000)))) (orderedInterval (-1068998503 / 1000000000000) (-1068998480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (74103191456553 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (301225359184713 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (201204579928167 / 800000000000) 2 (IntervalRat.scale (405 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000)))) (orderedInterval (15796505438 / 1000000000000) (15796505698 / 1000000000000))) = true
  rfl'

theorem compactCertificate330_chunkChecks2 :
    compactCertificate330.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate330.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate330_chunkChecks2_0
    compactCertificate330_chunkChecks2_1 compactCertificate330_chunkChecks2_2

theorem compactCertificate330_chunkChecks3_0 :
    compactCertificate330.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (405 / 2) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (119328466779981 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (38588374398573 / 160000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000)))) (orderedInterval (18536310103 / 1000000000000) (18536345567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (34819748996967 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (93530743608699 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (253954163218383 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000)))) (orderedInterval (-7252812925 / 1000000000000) (-7252812867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (187061487217479 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (320533046708067 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (236103191456553 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000)))) (orderedInterval (4622731971 / 1000000000000) (4622733490 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate330_chunkChecks3_1 :
    compactCertificate330.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (362243012354919 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (209141100695151 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (371124553259259 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000)))) (orderedInterval (-33533967393 / 1000000000000) (-33533966564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (346752698665671 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (247459087527543 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (280592230826097 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000)))) (orderedInterval (15751483961 / 1000000000000) (15751512878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (233928548852193 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (206682967252053 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (59904779765247 / 160000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000)))) (orderedInterval (2547257767 / 1000000000000) (2547257840 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate330_chunkChecks3_2 :
    compactCertificate330.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (165699773446509 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (140465533025349 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (87896808543447 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000)))) (orderedInterval (10281201461 / 1000000000000) (10281201506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (47271195966249 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (128350492605747 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (175251624632019 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000)))) (orderedInterval (4798362659 / 1000000000000) (4798362683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (74103191456553 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (301225359184713 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (201204579928167 / 800000000000) 3 (IntervalRat.scale (405 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000)))) (orderedInterval (30562571774 / 1000000000000) (30562572020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate330_chunkChecks3 :
    compactCertificate330.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate330.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate330_chunkChecks3_0
    compactCertificate330_chunkChecks3_1 compactCertificate330_chunkChecks3_2

theorem compactCertificate330_chunkChecks4_0 :
    compactCertificate330.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (405 / 2) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44566179324 / 1000000000000) (44566267333 / 1000000000000), orderedInterval (-34134343647 / 1000000000000) (-34134255639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (119328466779981 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49137272543 / 1000000000000) (-49137168966 / 1000000000000), orderedInterval (43217487486 / 1000000000000) (43217591063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (38588374398573 / 160000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3059533538 / 1000000000000) (-3059533537 / 1000000000000), orderedInterval (-51279896302 / 1000000000000) (-51279896300 / 1000000000000)))) (orderedInterval (16984952227 / 1000000000000) (16984987766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (34819748996967 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38606519763 / 1000000000000) (38606519765 / 1000000000000), orderedInterval (114173052793 / 1000000000000) (114173052794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (93530743608699 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73329365864 / 1000000000000) (-73329365857 / 1000000000000), orderedInterval (-7931351153 / 1000000000000) (-7931351147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (253954163218383 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35813944136 / 1000000000000) (-35813944135 / 1000000000000), orderedInterval (-26828981283 / 1000000000000) (-26828981282 / 1000000000000)))) (orderedInterval (15148284954 / 1000000000000) (15148285043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (187061487217479 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44123260069 / 1000000000000) (44123306822 / 1000000000000), orderedInterval (-27946570432 / 1000000000000) (-27946523679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (320533046708067 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24830085749 / 1000000000000) (-24830079677 / 1000000000000), orderedInterval (31213829849 / 1000000000000) (31213835921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (236103191456553 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26387355506 / 1000000000000) (26387355507 / 1000000000000), orderedInterval (38175689133 / 1000000000000) (38175689134 / 1000000000000)))) (orderedInterval (14569151650 / 1000000000000) (14569154653 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate330_chunkChecks4_1 :
    compactCertificate330.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (362243012354919 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34941555656 / 1000000000000) (34941555658 / 1000000000000), orderedInterval (13564275008 / 1000000000000) (13564275010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (209141100695151 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49039997792 / 1000000000000) (-49039997771 / 1000000000000), orderedInterval (-5406418582 / 1000000000000) (-5406418561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (371124553259259 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9698482676 / 1000000000000) (-9698482652 / 1000000000000), orderedInterval (35762997233 / 1000000000000) (35762997256 / 1000000000000)))) (orderedInterval (-202952068528 / 1000000000000) (-202952066685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (346752698665671 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24282298305 / 1000000000000) (24282298306 / 1000000000000), orderedInterval (29622085624 / 1000000000000) (29622085625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (247459087527543 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35783893784 / 1000000000000) (35783978968 / 1000000000000), orderedInterval (-27943546863 / 1000000000000) (-27943461680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (280592230826097 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13928162755 / 1000000000000) (-13928162611 / 1000000000000), orderedInterval (40282521434 / 1000000000000) (40282521579 / 1000000000000)))) (orderedInterval (9700162521 / 1000000000000) (9700206858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (233928548852193 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39942208190 / 1000000000000) (-39942208189 / 1000000000000), orderedInterval (-24051427623 / 1000000000000) (-24051427622 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (206682967252053 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49594663933 / 1000000000000) (49594663989 / 1000000000000), orderedInterval (2026506248 / 1000000000000) (2026506304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (59904779765247 / 160000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40145807078 / 1000000000000) (-40145807070 / 1000000000000), orderedInterval (-9362543952 / 1000000000000) (-9362543944 / 1000000000000)))) (orderedInterval (-21561820185 / 1000000000000) (-21561820071 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate330_chunkChecks4_2 :
    compactCertificate330.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (165699773446509 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29655198318 / 1000000000000) (29655198319 / 1000000000000), orderedInterval (46770477528 / 1000000000000) (46770477529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (140465533025349 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25506654324 / 1000000000000) (25506654325 / 1000000000000), orderedInterval (54472674996 / 1000000000000) (54472674997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (87896808543447 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49010098624 / 1000000000000) (-49010098623 / 1000000000000), orderedInterval (-58020145217 / 1000000000000) (-58020145216 / 1000000000000)))) (orderedInterval (-6245520499 / 1000000000000) (-6245520455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (47271195966249 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18788477029 / 1000000000000) (-18788477028 / 1000000000000), orderedInterval (-101925637738 / 1000000000000) (-101925637737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (128350492605747 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53057234448 / 1000000000000) (-53057234447 / 1000000000000), orderedInterval (-33789474702 / 1000000000000) (-33789474701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (175251624632019 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3347011638 / 1000000000000) (-3347011631 / 1000000000000), orderedInterval (53811805612 / 1000000000000) (53811805619 / 1000000000000)))) (orderedInterval (780707112 / 1000000000000) (780707137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (74103191456553 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61440409392 / 1000000000000) (-61440297239 / 1000000000000), orderedInterval (55990043142 / 1000000000000) (55990155296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (301225359184713 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13154751893 / 1000000000000) (13154751894 / 1000000000000), orderedInterval (38940207557 / 1000000000000) (38940207558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (201204579928167 / 800000000000) 4 (IntervalRat.scale (405 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41307126789 / 1000000000000) (41307126790 / 1000000000000), orderedInterval (28639880209 / 1000000000000) (28639880210 / 1000000000000)))) (orderedInterval (-31560164844 / 1000000000000) (-31560164523 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate330_chunkChecks4 :
    compactCertificate330.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate330.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate330_chunkChecks4_0
    compactCertificate330_chunkChecks4_1 compactCertificate330_chunkChecks4_2

theorem compactCertificate330_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate330.chunkCheck r b = true :=
  compactCertificate330.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate330_chunkChecks0
    · exact compactCertificate330_chunkChecks1
    · exact compactCertificate330_chunkChecks2
    · exact compactCertificate330_chunkChecks3
    · exact compactCertificate330_chunkChecks4)

theorem compactCertificate330_coefficient0 :
    compactCertificate330.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate330_coefficient1 :
    compactCertificate330.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate330_coefficient2 :
    compactCertificate330.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate330_coefficient3 :
    compactCertificate330.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate330_coefficient4 :
    compactCertificate330.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate330_coefficients : ∀ r : Fin 5,
    compactCertificate330.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate330_coefficient0
  · exact compactCertificate330_coefficient1
  · exact compactCertificate330_coefficient2
  · exact compactCertificate330_coefficient3
  · exact compactCertificate330_coefficient4

theorem compactCertificate330_lower : (1 : ℚ) ≤ compactCertificate330.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate330, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate330_proves {t : ℝ} (ht : t ∈ compactCertificate330.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate330.proves compactCertificate330_states compactCertificate330_chunks
    compactCertificate330_coefficients compactCertificate330_lower ht

end Erdos232
