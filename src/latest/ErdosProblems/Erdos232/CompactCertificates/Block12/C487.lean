/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate487 : CompactCertificate where
  left := 358
  right := 359
  center := 717 / 2
  grid := fun i =>
    match i.val with
    | 0 => 114
    | 1 => 84
    | 2 => 136
    | 3 => 25
    | 4 => 66
    | 5 => 179
    | 6 => 132
    | 7 => 226
    | 8 => 166
    | 9 => 255
    | 10 => 147
    | 11 => 262
    | 12 => 244
    | 13 => 174
    | 14 => 198
    | 15 => 165
    | 16 => 146
    | 17 => 211
    | 18 => 117
    | 19 => 99
    | 20 => 62
    | 21 => 33
    | 22 => 90
    | 23 => 124
    | 24 => 52
    | 25 => 212
    | _ => 142
  point := fun i =>
    match i.val with
    | 0 => 717 / 2
    | 1 => 1056277909645017 / 4000000000000
    | 2 => 341578573379961 / 800000000000
    | 3 => 308219259639819 / 4000000000000
    | 4 => 827920286017743 / 4000000000000
    | 5 => 2247964629970131 / 4000000000000
    | 6 => 1655840572036203 / 4000000000000
    | 7 => 2837311043082519 / 4000000000000
    | 8 => 2089950472522821 / 4000000000000
    | 9 => 3206521479734283 / 4000000000000
    | 10 => 1851286039486707 / 4000000000000
    | 11 => 3285139564035663 / 4000000000000
    | 12 => 3069403517818347 / 4000000000000
    | 13 => 2190471182188251 / 4000000000000
    | 14 => 2483760858053229 / 4000000000000
    | 15 => 2070700858358301 / 4000000000000
    | 16 => 1829527006416321 / 4000000000000
    | 17 => 530268235699779 / 800000000000
    | 18 => 1466749846433913 / 4000000000000
    | 19 => 1243380088631793 / 4000000000000
    | 20 => 778049527477179 / 4000000000000
    | 21 => 418437623553093 / 4000000000000
    | 22 => 1136139545658279 / 4000000000000
    | 23 => 1551301418038983 / 4000000000000
    | 24 => 655950472522821 / 4000000000000
    | 25 => 2666402253523941 / 4000000000000
    | _ => 1781033133438219 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))
    | 1 => (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))
    | 2 => (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000))
    | 3 => (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))
    | 4 => (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
    | 5 => (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000))
    | 6 => (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))
    | 7 => (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))
    | 8 => (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000))
    | 9 => (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))
    | 10 => (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))
    | 11 => (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000))
    | 12 => (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))
    | 13 => (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))
    | 14 => (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000))
    | 15 => (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))
    | 16 => (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))
    | 17 => (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000))
    | 18 => (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))
    | 19 => (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))
    | 20 => (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000))
    | 21 => (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))
    | 22 => (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))
    | 23 => (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000))
    | 24 => (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))
    | 25 => (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))
    | _ => (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16665698114 / 1000000000000) (16665698140 / 1000000000000)
      | 1 => orderedInterval (1189155915 / 1000000000000) (1189156377 / 1000000000000)
      | 2 => orderedInterval (722963366 / 1000000000000) (722963524 / 1000000000000)
      | 3 => orderedInterval (-1230459553 / 1000000000000) (-1230455529 / 1000000000000)
      | 4 => orderedInterval (2692566746 / 1000000000000) (2692567445 / 1000000000000)
      | 5 => orderedInterval (457044772 / 1000000000000) (457044845 / 1000000000000)
      | 6 => orderedInterval (1770961153 / 1000000000000) (1770961244 / 1000000000000)
      | 7 => orderedInterval (3005001596 / 1000000000000) (3005008887 / 1000000000000)
      | _ => orderedInterval (-1648450029 / 1000000000000) (-1648449920 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9458001607 / 1000000000000) (9458001636 / 1000000000000)
      | 1 => orderedInterval (4635273819 / 1000000000000) (4635273958 / 1000000000000)
      | 2 => orderedInterval (-2059001976 / 1000000000000) (-2059001740 / 1000000000000)
      | 3 => orderedInterval (8364602344 / 1000000000000) (8364611133 / 1000000000000)
      | 4 => orderedInterval (-1206980327 / 1000000000000) (-1206979222 / 1000000000000)
      | 5 => orderedInterval (-4044620728 / 1000000000000) (-4044620629 / 1000000000000)
      | 6 => orderedInterval (9477119251 / 1000000000000) (9477119335 / 1000000000000)
      | 7 => orderedInterval (-1616821946 / 1000000000000) (-1616814301 / 1000000000000)
      | _ => orderedInterval (-9705778323 / 1000000000000) (-9705778166 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16976600974 / 1000000000000) (-16976600941 / 1000000000000)
      | 1 => orderedInterval (-2716396126 / 1000000000000) (-2716396038 / 1000000000000)
      | 2 => orderedInterval (-1343242478 / 1000000000000) (-1343242122 / 1000000000000)
      | 3 => orderedInterval (-1965878668 / 1000000000000) (-1965859068 / 1000000000000)
      | 4 => orderedInterval (-5143367421 / 1000000000000) (-5143365648 / 1000000000000)
      | 5 => orderedInterval (248189235 / 1000000000000) (248189372 / 1000000000000)
      | 6 => orderedInterval (-752003927 / 1000000000000) (-752003847 / 1000000000000)
      | 7 => orderedInterval (-2476530710 / 1000000000000) (-2476522605 / 1000000000000)
      | _ => orderedInterval (7782642309 / 1000000000000) (7782642547 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10311997290 / 1000000000000) (-10311997252 / 1000000000000)
      | 1 => orderedInterval (-8725353148 / 1000000000000) (-8725353042 / 1000000000000)
      | 2 => orderedInterval (7630116408 / 1000000000000) (7630116949 / 1000000000000)
      | 3 => orderedInterval (-40369776065 / 1000000000000) (-40369731891 / 1000000000000)
      | 4 => orderedInterval (2965414673 / 1000000000000) (2965417559 / 1000000000000)
      | 5 => orderedInterval (8779840415 / 1000000000000) (8779840610 / 1000000000000)
      | 6 => orderedInterval (-8719413989 / 1000000000000) (-8719413911 / 1000000000000)
      | 7 => orderedInterval (2052983960 / 1000000000000) (2052992580 / 1000000000000)
      | _ => orderedInterval (16782450495 / 1000000000000) (16782450872 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17561432592 / 1000000000000) (17561432636 / 1000000000000)
      | 1 => orderedInterval (6178814842 / 1000000000000) (6178815000 / 1000000000000)
      | 2 => orderedInterval (2092061485 / 1000000000000) (2092062319 / 1000000000000)
      | 3 => orderedInterval (20418357086 / 1000000000000) (20418457433 / 1000000000000)
      | 4 => orderedInterval (6736095697 / 1000000000000) (6736100492 / 1000000000000)
      | 5 => orderedInterval (-3763541327 / 1000000000000) (-3763541044 / 1000000000000)
      | 6 => orderedInterval (277634885 / 1000000000000) (277634962 / 1000000000000)
      | 7 => orderedInterval (3080484559 / 1000000000000) (3080493791 / 1000000000000)
      | _ => orderedInterval (-28474099099 / 1000000000000) (-28474098480 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (23624482080 / 1000000000000) (23624495013 / 1000000000000)
    | 1 => orderedInterval (13301793721 / 1000000000000) (13301812004 / 1000000000000)
    | 2 => orderedInterval (-23343188760 / 1000000000000) (-23343158350 / 1000000000000)
    | 3 => orderedInterval (-29915734541 / 1000000000000) (-29915677526 / 1000000000000)
    | _ => orderedInterval (24107240720 / 1000000000000) (24107357109 / 1000000000000)

theorem compactCertificate487_stateChecks0 :
    compactCertificate487.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (717 / 2)) (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1056277909645017 / 4000000000000)) (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (341578573379961 / 800000000000)) (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks1 :
    compactCertificate487.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (308219259639819 / 4000000000000)) (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (827920286017743 / 4000000000000)) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2247964629970131 / 4000000000000)) (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks2 :
    compactCertificate487.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1655840572036203 / 4000000000000)) (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2837311043082519 / 4000000000000)) (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2089950472522821 / 4000000000000)) (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks3 :
    compactCertificate487.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3206521479734283 / 4000000000000)) (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1851286039486707 / 4000000000000)) (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3285139564035663 / 4000000000000)) (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks4 :
    compactCertificate487.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3069403517818347 / 4000000000000)) (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2190471182188251 / 4000000000000)) (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2483760858053229 / 4000000000000)) (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks5 :
    compactCertificate487.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2070700858358301 / 4000000000000)) (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1829527006416321 / 4000000000000)) (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (530268235699779 / 800000000000)) (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks6 :
    compactCertificate487.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1466749846433913 / 4000000000000)) (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1243380088631793 / 4000000000000)) (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (778049527477179 / 4000000000000)) (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks7 :
    compactCertificate487.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (418437623553093 / 4000000000000)) (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1136139545658279 / 4000000000000)) (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1551301418038983 / 4000000000000)) (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_stateChecks8 :
    compactCertificate487.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (655950472522821 / 4000000000000)) (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2666402253523941 / 4000000000000)) (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1781033133438219 / 4000000000000)) (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_states : ∀ j,
    BesselStateValid (compactCertificate487.point j) (compactCertificate487.state j) :=
  compactCertificate487.statesValid_of_checks3 compactCertificate487_stateChecks0
    compactCertificate487_stateChecks1 compactCertificate487_stateChecks2
    compactCertificate487_stateChecks3 compactCertificate487_stateChecks4
    compactCertificate487_stateChecks5 compactCertificate487_stateChecks6
    compactCertificate487_stateChecks7 compactCertificate487_stateChecks8

theorem compactCertificate487_chunkChecks0_0 :
    compactCertificate487.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (717 / 2) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1056277909645017 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (341578573379961 / 800000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000)))) (orderedInterval (16665698114 / 1000000000000) (16665698140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (308219259639819 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2247964629970131 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000)))) (orderedInterval (1189155915 / 1000000000000) (1189156377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1655840572036203 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2837311043082519 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2089950472522821 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000)))) (orderedInterval (722963366 / 1000000000000) (722963524 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks0_1 :
    compactCertificate487.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3206521479734283 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1851286039486707 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3285139564035663 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000)))) (orderedInterval (-1230459553 / 1000000000000) (-1230455529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3069403517818347 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2190471182188251 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2483760858053229 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000)))) (orderedInterval (2692566746 / 1000000000000) (2692567445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2070700858358301 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1829527006416321 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (530268235699779 / 800000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000)))) (orderedInterval (457044772 / 1000000000000) (457044845 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks0_2 :
    compactCertificate487.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1466749846433913 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1243380088631793 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (778049527477179 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000)))) (orderedInterval (1770961153 / 1000000000000) (1770961244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (418437623553093 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1136139545658279 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1551301418038983 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000)))) (orderedInterval (3005001596 / 1000000000000) (3005008887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (655950472522821 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2666402253523941 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1781033133438219 / 4000000000000) 0 (IntervalRat.scale (717 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000)))) (orderedInterval (-1648450029 / 1000000000000) (-1648449920 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks0 :
    compactCertificate487.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate487.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate487_chunkChecks0_0
    compactCertificate487_chunkChecks0_1 compactCertificate487_chunkChecks0_2

theorem compactCertificate487_chunkChecks1_0 :
    compactCertificate487.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (717 / 2) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1056277909645017 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (341578573379961 / 800000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000)))) (orderedInterval (9458001607 / 1000000000000) (9458001636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (308219259639819 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2247964629970131 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000)))) (orderedInterval (4635273819 / 1000000000000) (4635273958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1655840572036203 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2837311043082519 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2089950472522821 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000)))) (orderedInterval (-2059001976 / 1000000000000) (-2059001740 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks1_1 :
    compactCertificate487.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3206521479734283 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1851286039486707 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3285139564035663 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000)))) (orderedInterval (8364602344 / 1000000000000) (8364611133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3069403517818347 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2190471182188251 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2483760858053229 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000)))) (orderedInterval (-1206980327 / 1000000000000) (-1206979222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2070700858358301 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1829527006416321 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (530268235699779 / 800000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000)))) (orderedInterval (-4044620728 / 1000000000000) (-4044620629 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks1_2 :
    compactCertificate487.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1466749846433913 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1243380088631793 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (778049527477179 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000)))) (orderedInterval (9477119251 / 1000000000000) (9477119335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (418437623553093 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1136139545658279 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1551301418038983 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000)))) (orderedInterval (-1616821946 / 1000000000000) (-1616814301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (655950472522821 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2666402253523941 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1781033133438219 / 4000000000000) 1 (IntervalRat.scale (717 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000)))) (orderedInterval (-9705778323 / 1000000000000) (-9705778166 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks1 :
    compactCertificate487.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate487.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate487_chunkChecks1_0
    compactCertificate487_chunkChecks1_1 compactCertificate487_chunkChecks1_2

theorem compactCertificate487_chunkChecks2_0 :
    compactCertificate487.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (717 / 2) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1056277909645017 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (341578573379961 / 800000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000)))) (orderedInterval (-16976600974 / 1000000000000) (-16976600941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (308219259639819 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2247964629970131 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000)))) (orderedInterval (-2716396126 / 1000000000000) (-2716396038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1655840572036203 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2837311043082519 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2089950472522821 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000)))) (orderedInterval (-1343242478 / 1000000000000) (-1343242122 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks2_1 :
    compactCertificate487.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3206521479734283 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1851286039486707 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3285139564035663 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000)))) (orderedInterval (-1965878668 / 1000000000000) (-1965859068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3069403517818347 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2190471182188251 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2483760858053229 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000)))) (orderedInterval (-5143367421 / 1000000000000) (-5143365648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2070700858358301 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1829527006416321 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (530268235699779 / 800000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000)))) (orderedInterval (248189235 / 1000000000000) (248189372 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks2_2 :
    compactCertificate487.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1466749846433913 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1243380088631793 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (778049527477179 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000)))) (orderedInterval (-752003927 / 1000000000000) (-752003847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (418437623553093 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1136139545658279 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1551301418038983 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000)))) (orderedInterval (-2476530710 / 1000000000000) (-2476522605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (655950472522821 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2666402253523941 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1781033133438219 / 4000000000000) 2 (IntervalRat.scale (717 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000)))) (orderedInterval (7782642309 / 1000000000000) (7782642547 / 1000000000000))) = true
  rfl'

theorem compactCertificate487_chunkChecks2 :
    compactCertificate487.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate487.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate487_chunkChecks2_0
    compactCertificate487_chunkChecks2_1 compactCertificate487_chunkChecks2_2

theorem compactCertificate487_chunkChecks3_0 :
    compactCertificate487.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (717 / 2) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1056277909645017 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (341578573379961 / 800000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000)))) (orderedInterval (-10311997290 / 1000000000000) (-10311997252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (308219259639819 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2247964629970131 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000)))) (orderedInterval (-8725353148 / 1000000000000) (-8725353042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1655840572036203 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2837311043082519 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2089950472522821 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000)))) (orderedInterval (7630116408 / 1000000000000) (7630116949 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate487_chunkChecks3_1 :
    compactCertificate487.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3206521479734283 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1851286039486707 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3285139564035663 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000)))) (orderedInterval (-40369776065 / 1000000000000) (-40369731891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3069403517818347 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2190471182188251 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2483760858053229 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000)))) (orderedInterval (2965414673 / 1000000000000) (2965417559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2070700858358301 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1829527006416321 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (530268235699779 / 800000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000)))) (orderedInterval (8779840415 / 1000000000000) (8779840610 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate487_chunkChecks3_2 :
    compactCertificate487.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1466749846433913 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1243380088631793 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (778049527477179 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000)))) (orderedInterval (-8719413989 / 1000000000000) (-8719413911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (418437623553093 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1136139545658279 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1551301418038983 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000)))) (orderedInterval (2052983960 / 1000000000000) (2052992580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (655950472522821 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2666402253523941 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1781033133438219 / 4000000000000) 3 (IntervalRat.scale (717 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000)))) (orderedInterval (16782450495 / 1000000000000) (16782450872 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate487_chunkChecks3 :
    compactCertificate487.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate487.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate487_chunkChecks3_0
    compactCertificate487_chunkChecks3_1 compactCertificate487_chunkChecks3_2

theorem compactCertificate487_chunkChecks4_0 :
    compactCertificate487.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (717 / 2) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38351009782 / 1000000000000) (38351009783 / 1000000000000), orderedInterval (17410368489 / 1000000000000) (17410368490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1056277909645017 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40239652624 / 1000000000000) (40239652625 / 1000000000000), orderedInterval (28058715091 / 1000000000000) (28058715092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (341578573379961 / 800000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18570615797 / 1000000000000) (18570615798 / 1000000000000), orderedInterval (33832929648 / 1000000000000) (33832929649 / 1000000000000)))) (orderedInterval (17561432592 / 1000000000000) (17561432636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (308219259639819 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58640695355 / 1000000000000) (58640733882 / 1000000000000), orderedInterval (-69829801080 / 1000000000000) (-69829762553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (827920286017743 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22601520419 / 1000000000000) (22601520420 / 1000000000000), orderedInterval (50590552005 / 1000000000000) (50590552006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2247964629970131 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14068791694 / 1000000000000) (-14068791693 / 1000000000000), orderedInterval (-30563006165 / 1000000000000) (-30563006164 / 1000000000000)))) (orderedInterval (6178814842 / 1000000000000) (6178815000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1655840572036203 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2156129541 / 1000000000000) (2156129542 / 1000000000000), orderedInterval (39153866398 / 1000000000000) (39153866399 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2837311043082519 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3379363068 / 1000000000000) (3379363069 / 1000000000000), orderedInterval (29764671074 / 1000000000000) (29764671075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2089950472522821 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34226892173 / 1000000000000) (34226897873 / 1000000000000), orderedInterval (-6885424499 / 1000000000000) (-6885418799 / 1000000000000)))) (orderedInterval (2092061485 / 1000000000000) (2092062319 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate487_chunkChecks4_1 :
    compactCertificate487.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3206521479734283 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27224098970 / 1000000000000) (-27224098844 / 1000000000000), orderedInterval (-7263442652 / 1000000000000) (-7263442526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1851286039486707 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36180079299 / 1000000000000) (-36180073951 / 1000000000000), orderedInterval (8195081884 / 1000000000000) (8195087232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3285139564035663 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23827411896 / 1000000000000) (-23827387537 / 1000000000000), orderedInterval (14416087602 / 1000000000000) (14416111962 / 1000000000000)))) (orderedInterval (20418357086 / 1000000000000) (20418457433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3069403517818347 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28799327827 / 1000000000000) (28799330940 / 1000000000000), orderedInterval (-500075070 / 1000000000000) (-500071957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2190471182188251 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33449312555 / 1000000000000) (33449318890 / 1000000000000), orderedInterval (-6638761759 / 1000000000000) (-6638755424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2483760858053229 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9765826105 / 1000000000000) (-9765826092 / 1000000000000), orderedInterval (30501801284 / 1000000000000) (30501801298 / 1000000000000)))) (orderedInterval (6736095697 / 1000000000000) (6736100492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2070700858358301 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3416629973 / 1000000000000) (-3416629972 / 1000000000000), orderedInterval (-34897902935 / 1000000000000) (-34897902934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1829527006416321 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18071078217 / 1000000000000) (-18071077545 / 1000000000000), orderedInterval (32658917642 / 1000000000000) (32658918314 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (530268235699779 / 800000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20998666742 / 1000000000000) (-20998666741 / 1000000000000), orderedInterval (-22776821833 / 1000000000000) (-22776821832 / 1000000000000)))) (orderedInterval (-3763541327 / 1000000000000) (-3763541044 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate487_chunkChecks4_2 :
    compactCertificate487.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1466749846433913 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3903527737 / 1000000000000) (3903527741 / 1000000000000), orderedInterval (-41489070552 / 1000000000000) (-41489070548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1243380088631793 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26012122160 / 1000000000000) (-26012122159 / 1000000000000), orderedInterval (-36990575873 / 1000000000000) (-36990575872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (778049527477179 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28346279525 / 1000000000000) (28346279526 / 1000000000000), orderedInterval (49620142632 / 1000000000000) (49620142633 / 1000000000000)))) (orderedInterval (277634885 / 1000000000000) (277634962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (418437623553093 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77131397090 / 1000000000000) (-77131396810 / 1000000000000), orderedInterval (12046200662 / 1000000000000) (12046200943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1136139545658279 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41416928669 / 1000000000000) (41416963776 / 1000000000000), orderedInterval (-23007140980 / 1000000000000) (-23007105873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1551301418038983 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32886559244 / 1000000000000) (-32886475131 / 1000000000000), orderedInterval (23706419956 / 1000000000000) (23706504069 / 1000000000000)))) (orderedInterval (3080484559 / 1000000000000) (3080493791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (655950472522821 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61497140844 / 1000000000000) (61497140848 / 1000000000000), orderedInterval (9822767661 / 1000000000000) (9822767666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2666402253523941 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30270983488 / 1000000000000) (30270983599 / 1000000000000), orderedInterval (6197556704 / 1000000000000) (6197556815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1781033133438219 / 4000000000000) 4 (IntervalRat.scale (717 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2371396776 / 1000000000000) (-2371396774 / 1000000000000), orderedInterval (37740624496 / 1000000000000) (37740624498 / 1000000000000)))) (orderedInterval (-28474099099 / 1000000000000) (-28474098480 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate487_chunkChecks4 :
    compactCertificate487.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate487.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate487_chunkChecks4_0
    compactCertificate487_chunkChecks4_1 compactCertificate487_chunkChecks4_2

theorem compactCertificate487_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate487.chunkCheck r b = true :=
  compactCertificate487.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate487_chunkChecks0
    · exact compactCertificate487_chunkChecks1
    · exact compactCertificate487_chunkChecks2
    · exact compactCertificate487_chunkChecks3
    · exact compactCertificate487_chunkChecks4)

theorem compactCertificate487_coefficient0 :
    compactCertificate487.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate487_coefficient1 :
    compactCertificate487.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate487_coefficient2 :
    compactCertificate487.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate487_coefficient3 :
    compactCertificate487.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate487_coefficient4 :
    compactCertificate487.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate487_coefficients : ∀ r : Fin 5,
    compactCertificate487.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate487_coefficient0
  · exact compactCertificate487_coefficient1
  · exact compactCertificate487_coefficient2
  · exact compactCertificate487_coefficient3
  · exact compactCertificate487_coefficient4

theorem compactCertificate487_lower : (1 : ℚ) ≤ compactCertificate487.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate487, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate487_proves {t : ℝ} (ht : t ∈ compactCertificate487.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate487.proves compactCertificate487_states compactCertificate487_chunks
    compactCertificate487_coefficients compactCertificate487_lower ht

end Erdos232
