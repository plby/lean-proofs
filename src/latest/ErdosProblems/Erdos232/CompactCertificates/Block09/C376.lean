/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate376 : CompactCertificate where
  left := 247
  right := 248
  center := 495 / 2
  grid := fun i =>
    match i.val with
    | 0 => 79
    | 1 => 58
    | 2 => 94
    | 3 => 17
    | 4 => 46
    | 5 => 124
    | 6 => 91
    | 7 => 156
    | 8 => 115
    | 9 => 176
    | 10 => 102
    | 11 => 181
    | 12 => 169
    | 13 => 120
    | 14 => 137
    | 15 => 114
    | 16 => 101
    | 17 => 146
    | 18 => 81
    | 19 => 68
    | 20 => 43
    | 21 => 23
    | 22 => 62
    | 23 => 85
    | 24 => 36
    | 25 => 147
    | _ => 98
  point := fun i =>
    match i.val with
    | 0 => 495 / 2
    | 1 => 145845903842199 / 800000000000
    | 2 => 47163568709367 / 160000000000
    | 3 => 42557470996293 / 800000000000
    | 4 => 114315353299521 / 800000000000
    | 5 => 310388421711357 / 800000000000
    | 6 => 228630706599141 / 800000000000
    | 7 => 391762612643193 / 800000000000
    | 8 => 288570567335787 / 800000000000
    | 9 => 442741459544901 / 800000000000
    | 10 => 255616900849629 / 800000000000
    | 11 => 453596676205761 / 800000000000
    | 12 => 423808853924709 / 800000000000
    | 13 => 302449995866997 / 800000000000
    | 14 => 342946059898563 / 800000000000
    | 15 => 285912670819347 / 800000000000
    | 16 => 252612515530287 / 800000000000
    | 17 => 73216953046413 / 160000000000
    | 18 => 202521945323511 / 800000000000
    | 19 => 171680095919871 / 800000000000
    | 20 => 107429432664213 / 800000000000
    | 21 => 57775906180971 / 800000000000
    | 22 => 156872824295913 / 800000000000
    | 23 => 214196430105801 / 800000000000
    | 24 => 90570567335787 / 800000000000
    | 25 => 368164327892427 / 800000000000
    | _ => 245916708801093 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))
    | 1 => (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))
    | 2 => (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000))
    | 3 => (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))
    | 4 => (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))
    | 5 => (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000))
    | 6 => (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))
    | 7 => (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))
    | 8 => (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000))
    | 9 => (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))
    | 10 => (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))
    | 11 => (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000))
    | 12 => (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))
    | 13 => (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))
    | 14 => (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000))
    | 15 => (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))
    | 16 => (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))
    | 17 => (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000))
    | 18 => (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))
    | 19 => (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))
    | 20 => (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000))
    | 21 => (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))
    | 22 => (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))
    | 23 => (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000))
    | 24 => (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))
    | 25 => (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))
    | _ => (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-895798932 / 1000000000000) (-895798914 / 1000000000000)
      | 1 => orderedInterval (876664734 / 1000000000000) (876669565 / 1000000000000)
      | 2 => orderedInterval (-649745352 / 1000000000000) (-649745338 / 1000000000000)
      | 3 => orderedInterval (-2672792478 / 1000000000000) (-2672790242 / 1000000000000)
      | 4 => orderedInterval (3332961467 / 1000000000000) (3332962437 / 1000000000000)
      | 5 => orderedInterval (-2000417298 / 1000000000000) (-2000416126 / 1000000000000)
      | 6 => orderedInterval (-7056079832 / 1000000000000) (-7056079239 / 1000000000000)
      | 7 => orderedInterval (3786376945 / 1000000000000) (3786377618 / 1000000000000)
      | _ => orderedInterval (-4429276964 / 1000000000000) (-4429275259 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16594605571 / 1000000000000) (-16594605550 / 1000000000000)
      | 1 => orderedInterval (-2029799346 / 1000000000000) (-2029795127 / 1000000000000)
      | 2 => orderedInterval (-3471075246 / 1000000000000) (-3471075221 / 1000000000000)
      | 3 => orderedInterval (-6701693227 / 1000000000000) (-6701688125 / 1000000000000)
      | 4 => orderedInterval (-232640414 / 1000000000000) (-232638866 / 1000000000000)
      | 5 => orderedInterval (4801837326 / 1000000000000) (4801838826 / 1000000000000)
      | 6 => orderedInterval (6361362766 / 1000000000000) (6361363358 / 1000000000000)
      | 7 => orderedInterval (1183746488 / 1000000000000) (1183747026 / 1000000000000)
      | _ => orderedInterval (-6152849504 / 1000000000000) (-6152846366 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (877279071 / 1000000000000) (877279094 / 1000000000000)
      | 1 => orderedInterval (-4430860357 / 1000000000000) (-4430855661 / 1000000000000)
      | 2 => orderedInterval (2169590584 / 1000000000000) (2169590628 / 1000000000000)
      | 3 => orderedInterval (11006893605 / 1000000000000) (11006905280 / 1000000000000)
      | 4 => orderedInterval (-7146015698 / 1000000000000) (-7146013210 / 1000000000000)
      | 5 => orderedInterval (3704052850 / 1000000000000) (3704054777 / 1000000000000)
      | 6 => orderedInterval (6493484733 / 1000000000000) (6493485330 / 1000000000000)
      | 7 => orderedInterval (-3764328411 / 1000000000000) (-3764327977 / 1000000000000)
      | _ => orderedInterval (11582433523 / 1000000000000) (11582439333 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15391462491 / 1000000000000) (15391462519 / 1000000000000)
      | 1 => orderedInterval (7534432303 / 1000000000000) (7534438538 / 1000000000000)
      | 2 => orderedInterval (10991912847 / 1000000000000) (10991912926 / 1000000000000)
      | 3 => orderedInterval (49361610219 / 1000000000000) (49361636921 / 1000000000000)
      | 4 => orderedInterval (-2357540454 / 1000000000000) (-2357536447 / 1000000000000)
      | 5 => orderedInterval (-11191153133 / 1000000000000) (-11191150659 / 1000000000000)
      | 6 => orderedInterval (-7448456844 / 1000000000000) (-7448456242 / 1000000000000)
      | 7 => orderedInterval (-689523721 / 1000000000000) (-689523369 / 1000000000000)
      | _ => orderedInterval (2280202989 / 1000000000000) (2280213746 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-643212990 / 1000000000000) (-643212958 / 1000000000000)
      | 1 => orderedInterval (12054635192 / 1000000000000) (12054644340 / 1000000000000)
      | 2 => orderedInterval (-7703170522 / 1000000000000) (-7703170376 / 1000000000000)
      | 3 => orderedInterval (-48150982196 / 1000000000000) (-48150920997 / 1000000000000)
      | 4 => orderedInterval (13973885928 / 1000000000000) (13973892431 / 1000000000000)
      | 5 => orderedInterval (-7578036836 / 1000000000000) (-7578033643 / 1000000000000)
      | 6 => orderedInterval (-6098072261 / 1000000000000) (-6098071650 / 1000000000000)
      | 7 => orderedInterval (4677141131 / 1000000000000) (4677141419 / 1000000000000)
      | _ => orderedInterval (-32649529000 / 1000000000000) (-32649509012 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9708107710 / 1000000000000) (-9708095498 / 1000000000000)
    | 1 => orderedInterval (-22835716728 / 1000000000000) (-22835700045 / 1000000000000)
    | 2 => orderedInterval (20492529900 / 1000000000000) (20492557594 / 1000000000000)
    | 3 => orderedInterval (63872946697 / 1000000000000) (63872997933 / 1000000000000)
    | _ => orderedInterval (-72117341554 / 1000000000000) (-72117240446 / 1000000000000)

theorem compactCertificate376_stateChecks0 :
    compactCertificate376.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (495 / 2)) (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (145845903842199 / 800000000000)) (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (47163568709367 / 160000000000)) (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks1 :
    compactCertificate376.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (42557470996293 / 800000000000)) (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (114315353299521 / 800000000000)) (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (310388421711357 / 800000000000)) (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks2 :
    compactCertificate376.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (228630706599141 / 800000000000)) (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (391762612643193 / 800000000000)) (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (288570567335787 / 800000000000)) (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks3 :
    compactCertificate376.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (442741459544901 / 800000000000)) (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (255616900849629 / 800000000000)) (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (453596676205761 / 800000000000)) (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks4 :
    compactCertificate376.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (423808853924709 / 800000000000)) (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (302449995866997 / 800000000000)) (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (342946059898563 / 800000000000)) (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks5 :
    compactCertificate376.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (285912670819347 / 800000000000)) (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (252612515530287 / 800000000000)) (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (73216953046413 / 160000000000)) (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks6 :
    compactCertificate376.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (202521945323511 / 800000000000)) (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (171680095919871 / 800000000000)) (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (107429432664213 / 800000000000)) (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks7 :
    compactCertificate376.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (57775906180971 / 800000000000)) (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (156872824295913 / 800000000000)) (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (214196430105801 / 800000000000)) (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_stateChecks8 :
    compactCertificate376.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (90570567335787 / 800000000000)) (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (368164327892427 / 800000000000)) (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (245916708801093 / 800000000000)) (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_states : ∀ j,
    BesselStateValid (compactCertificate376.point j) (compactCertificate376.state j) :=
  compactCertificate376.statesValid_of_checks3 compactCertificate376_stateChecks0
    compactCertificate376_stateChecks1 compactCertificate376_stateChecks2
    compactCertificate376_stateChecks3 compactCertificate376_stateChecks4
    compactCertificate376_stateChecks5 compactCertificate376_stateChecks6
    compactCertificate376_stateChecks7 compactCertificate376_stateChecks8

theorem compactCertificate376_chunkChecks0_0 :
    compactCertificate376.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (495 / 2) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (145845903842199 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (47163568709367 / 160000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000)))) (orderedInterval (-895798932 / 1000000000000) (-895798914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (42557470996293 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (114315353299521 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (310388421711357 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000)))) (orderedInterval (876664734 / 1000000000000) (876669565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (228630706599141 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (391762612643193 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (288570567335787 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000)))) (orderedInterval (-649745352 / 1000000000000) (-649745338 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks0_1 :
    compactCertificate376.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (442741459544901 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (255616900849629 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (453596676205761 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000)))) (orderedInterval (-2672792478 / 1000000000000) (-2672790242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (423808853924709 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (302449995866997 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (342946059898563 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000)))) (orderedInterval (3332961467 / 1000000000000) (3332962437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (285912670819347 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (252612515530287 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (73216953046413 / 160000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000)))) (orderedInterval (-2000417298 / 1000000000000) (-2000416126 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks0_2 :
    compactCertificate376.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (202521945323511 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (171680095919871 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (107429432664213 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000)))) (orderedInterval (-7056079832 / 1000000000000) (-7056079239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (57775906180971 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (156872824295913 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (214196430105801 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000)))) (orderedInterval (3786376945 / 1000000000000) (3786377618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (90570567335787 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (368164327892427 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (245916708801093 / 800000000000) 0 (IntervalRat.scale (495 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000)))) (orderedInterval (-4429276964 / 1000000000000) (-4429275259 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks0 :
    compactCertificate376.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate376.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate376_chunkChecks0_0
    compactCertificate376_chunkChecks0_1 compactCertificate376_chunkChecks0_2

theorem compactCertificate376_chunkChecks1_0 :
    compactCertificate376.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (495 / 2) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (145845903842199 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (47163568709367 / 160000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000)))) (orderedInterval (-16594605571 / 1000000000000) (-16594605550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (42557470996293 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (114315353299521 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (310388421711357 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000)))) (orderedInterval (-2029799346 / 1000000000000) (-2029795127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (228630706599141 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (391762612643193 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (288570567335787 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000)))) (orderedInterval (-3471075246 / 1000000000000) (-3471075221 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks1_1 :
    compactCertificate376.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (442741459544901 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (255616900849629 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (453596676205761 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000)))) (orderedInterval (-6701693227 / 1000000000000) (-6701688125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (423808853924709 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (302449995866997 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (342946059898563 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000)))) (orderedInterval (-232640414 / 1000000000000) (-232638866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (285912670819347 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (252612515530287 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (73216953046413 / 160000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000)))) (orderedInterval (4801837326 / 1000000000000) (4801838826 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks1_2 :
    compactCertificate376.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (202521945323511 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (171680095919871 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (107429432664213 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000)))) (orderedInterval (6361362766 / 1000000000000) (6361363358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (57775906180971 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (156872824295913 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (214196430105801 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000)))) (orderedInterval (1183746488 / 1000000000000) (1183747026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (90570567335787 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (368164327892427 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (245916708801093 / 800000000000) 1 (IntervalRat.scale (495 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000)))) (orderedInterval (-6152849504 / 1000000000000) (-6152846366 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks1 :
    compactCertificate376.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate376.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate376_chunkChecks1_0
    compactCertificate376_chunkChecks1_1 compactCertificate376_chunkChecks1_2

theorem compactCertificate376_chunkChecks2_0 :
    compactCertificate376.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (495 / 2) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (145845903842199 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (47163568709367 / 160000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000)))) (orderedInterval (877279071 / 1000000000000) (877279094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (42557470996293 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (114315353299521 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (310388421711357 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000)))) (orderedInterval (-4430860357 / 1000000000000) (-4430855661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (228630706599141 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (391762612643193 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (288570567335787 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000)))) (orderedInterval (2169590584 / 1000000000000) (2169590628 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks2_1 :
    compactCertificate376.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (442741459544901 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (255616900849629 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (453596676205761 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000)))) (orderedInterval (11006893605 / 1000000000000) (11006905280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (423808853924709 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (302449995866997 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (342946059898563 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000)))) (orderedInterval (-7146015698 / 1000000000000) (-7146013210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (285912670819347 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (252612515530287 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (73216953046413 / 160000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000)))) (orderedInterval (3704052850 / 1000000000000) (3704054777 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks2_2 :
    compactCertificate376.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (202521945323511 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (171680095919871 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (107429432664213 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000)))) (orderedInterval (6493484733 / 1000000000000) (6493485330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (57775906180971 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (156872824295913 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (214196430105801 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000)))) (orderedInterval (-3764328411 / 1000000000000) (-3764327977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (90570567335787 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (368164327892427 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (245916708801093 / 800000000000) 2 (IntervalRat.scale (495 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000)))) (orderedInterval (11582433523 / 1000000000000) (11582439333 / 1000000000000))) = true
  rfl'

theorem compactCertificate376_chunkChecks2 :
    compactCertificate376.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate376.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate376_chunkChecks2_0
    compactCertificate376_chunkChecks2_1 compactCertificate376_chunkChecks2_2

theorem compactCertificate376_chunkChecks3_0 :
    compactCertificate376.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (495 / 2) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (145845903842199 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (47163568709367 / 160000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000)))) (orderedInterval (15391462491 / 1000000000000) (15391462519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (42557470996293 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (114315353299521 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (310388421711357 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000)))) (orderedInterval (7534432303 / 1000000000000) (7534438538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (228630706599141 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (391762612643193 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (288570567335787 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000)))) (orderedInterval (10991912847 / 1000000000000) (10991912926 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate376_chunkChecks3_1 :
    compactCertificate376.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (442741459544901 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (255616900849629 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (453596676205761 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000)))) (orderedInterval (49361610219 / 1000000000000) (49361636921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (423808853924709 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (302449995866997 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (342946059898563 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000)))) (orderedInterval (-2357540454 / 1000000000000) (-2357536447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (285912670819347 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (252612515530287 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (73216953046413 / 160000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000)))) (orderedInterval (-11191153133 / 1000000000000) (-11191150659 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate376_chunkChecks3_2 :
    compactCertificate376.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (202521945323511 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (171680095919871 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (107429432664213 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000)))) (orderedInterval (-7448456844 / 1000000000000) (-7448456242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (57775906180971 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (156872824295913 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (214196430105801 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000)))) (orderedInterval (-689523721 / 1000000000000) (-689523369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (90570567335787 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (368164327892427 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (245916708801093 / 800000000000) 3 (IntervalRat.scale (495 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000)))) (orderedInterval (2280202989 / 1000000000000) (2280213746 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate376_chunkChecks3 :
    compactCertificate376.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate376.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate376_chunkChecks3_0
    compactCertificate376_chunkChecks3_1 compactCertificate376_chunkChecks3_2

theorem compactCertificate376_chunkChecks4_0 :
    compactCertificate376.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (495 / 2) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5016476065 / 1000000000000) (-5016476064 / 1000000000000), orderedInterval (-50458085593 / 1000000000000) (-50458085591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (145845903842199 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45534782112 / 1000000000000) (45534782113 / 1000000000000), orderedInterval (37539347760 / 1000000000000) (37539347761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (47163568709367 / 160000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11387998689 / 1000000000000) (11387998690 / 1000000000000), orderedInterval (45036385749 / 1000000000000) (45036385750 / 1000000000000)))) (orderedInterval (-643212990 / 1000000000000) (-643212958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (42557470996293 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59290488693 / 1000000000000) (-59290488692 / 1000000000000), orderedInterval (-91378100093 / 1000000000000) (-91378100092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (114315353299521 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49459029342 / 1000000000000) (-49458936919 / 1000000000000), orderedInterval (44994759062 / 1000000000000) (44994851484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (310388421711357 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28685500421 / 1000000000000) (-28685480351 / 1000000000000), orderedInterval (28637244183 / 1000000000000) (28637264253 / 1000000000000)))) (orderedInterval (12054635192 / 1000000000000) (12054644340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (228630706599141 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29985034175 / 1000000000000) (-29985034174 / 1000000000000), orderedInterval (-36395995059 / 1000000000000) (-36395995058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (391762612643193 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14039232597 / 1000000000000) (14039232598 / 1000000000000), orderedInterval (33195780104 / 1000000000000) (33195780105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (288570567335787 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8967187954 / 1000000000000) (-8967187953 / 1000000000000), orderedInterval (-41030021978 / 1000000000000) (-41030021977 / 1000000000000)))) (orderedInterval (-7703170522 / 1000000000000) (-7703170376 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate376_chunkChecks4_1 :
    compactCertificate376.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (442741459544901 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32603910334 / 1000000000000) (32603910349 / 1000000000000), orderedInterval (9314415134 / 1000000000000) (9314415150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (255616900849629 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6065913521 / 1000000000000) (-6065913511 / 1000000000000), orderedInterval (44231946277 / 1000000000000) (44231946287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (453596676205761 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25113015054 / 1000000000000) (25113030072 / 1000000000000), orderedInterval (-22206166563 / 1000000000000) (-22206151545 / 1000000000000)))) (orderedInterval (-48150982196 / 1000000000000) (-48150920997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (423808853924709 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12952449198 / 1000000000000) (12952449280 / 1000000000000), orderedInterval (-32167248968 / 1000000000000) (-32167248886 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (302449995866997 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39372562211 / 1000000000000) (39372568861 / 1000000000000), orderedInterval (-11614977762 / 1000000000000) (-11614971112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (342946059898563 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30903369878 / 1000000000000) (30903431006 / 1000000000000), orderedInterval (-23058682738 / 1000000000000) (-23058621610 / 1000000000000)))) (orderedInterval (13973885928 / 1000000000000) (13973892431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (285912670819347 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1448391942 / 1000000000000) (1448391943 / 1000000000000), orderedInterval (42178566613 / 1000000000000) (42178566614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (252612515530287 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30613287034 / 1000000000000) (30613307081 / 1000000000000), orderedInterval (-32895720868 / 1000000000000) (-32895700821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (73216953046413 / 160000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10359534456 / 1000000000000) (-10359534425 / 1000000000000), orderedInterval (35842551109 / 1000000000000) (35842551140 / 1000000000000)))) (orderedInterval (-7578036836 / 1000000000000) (-7578033643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate376_chunkChecks4_2 :
    compactCertificate376.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (202521945323511 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25423364312 / 1000000000000) (25423367315 / 1000000000000), orderedInterval (-43275478224 / 1000000000000) (-43275475222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (171680095919871 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53528060550 / 1000000000000) (53528061426 / 1000000000000), orderedInterval (-10188455899 / 1000000000000) (-10188455023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (107429432664213 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1185995502 / 1000000000000) (1185995509 / 1000000000000), orderedInterval (-68847525795 / 1000000000000) (-68847525788 / 1000000000000)))) (orderedInterval (-6098072261 / 1000000000000) (-6098071650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (57775906180971 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63785224291 / 1000000000000) (-63785224290 / 1000000000000), orderedInterval (-68453135477 / 1000000000000) (-68453135476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (156872824295913 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49269043333 / 1000000000000) (49269071565 / 1000000000000), orderedInterval (-28745684904 / 1000000000000) (-28745656672 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (214196430105801 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48622010744 / 1000000000000) (-48622010707 / 1000000000000), orderedInterval (-3597084895 / 1000000000000) (-3597084857 / 1000000000000)))) (orderedInterval (4677141131 / 1000000000000) (4677141419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (90570567335787 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (58747614680 / 1000000000000) (58747614681 / 1000000000000), orderedInterval (46344183480 / 1000000000000) (46344183481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (368164327892427 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27284432960 / 1000000000000) (27284453052 / 1000000000000), orderedInterval (-25306073373 / 1000000000000) (-25306053281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (245916708801093 / 800000000000) 4 (IntervalRat.scale (495 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13657044652 / 1000000000000) (13657044653 / 1000000000000), orderedInterval (43388577097 / 1000000000000) (43388577098 / 1000000000000)))) (orderedInterval (-32649529000 / 1000000000000) (-32649509012 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate376_chunkChecks4 :
    compactCertificate376.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate376.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate376_chunkChecks4_0
    compactCertificate376_chunkChecks4_1 compactCertificate376_chunkChecks4_2

theorem compactCertificate376_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate376.chunkCheck r b = true :=
  compactCertificate376.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate376_chunkChecks0
    · exact compactCertificate376_chunkChecks1
    · exact compactCertificate376_chunkChecks2
    · exact compactCertificate376_chunkChecks3
    · exact compactCertificate376_chunkChecks4)

theorem compactCertificate376_coefficient0 :
    compactCertificate376.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate376_coefficient1 :
    compactCertificate376.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate376_coefficient2 :
    compactCertificate376.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate376_coefficient3 :
    compactCertificate376.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate376_coefficient4 :
    compactCertificate376.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate376_coefficients : ∀ r : Fin 5,
    compactCertificate376.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate376_coefficient0
  · exact compactCertificate376_coefficient1
  · exact compactCertificate376_coefficient2
  · exact compactCertificate376_coefficient3
  · exact compactCertificate376_coefficient4

theorem compactCertificate376_lower : (1 : ℚ) ≤ compactCertificate376.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate376, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate376_proves {t : ℝ} (ht : t ∈ compactCertificate376.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate376.proves compactCertificate376_states compactCertificate376_chunks
    compactCertificate376_coefficients compactCertificate376_lower ht

end Erdos232
