/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate449 : CompactCertificate where
  left := 320
  right := 321
  center := 641 / 2
  grid := fun i =>
    match i.val with
    | 0 => 102
    | 1 => 75
    | 2 => 122
    | 3 => 22
    | 4 => 59
    | 5 => 160
    | 6 => 118
    | 7 => 202
    | 8 => 149
    | 9 => 228
    | 10 => 132
    | 11 => 234
    | 12 => 218
    | 13 => 156
    | 14 => 177
    | 15 => 147
    | 16 => 130
    | 17 => 189
    | 18 => 104
    | 19 => 89
    | 20 => 55
    | 21 => 30
    | 22 => 81
    | 23 => 110
    | 24 => 47
    | 25 => 190
    | _ => 127
  point := fun i =>
    match i.val with
    | 0 => 641 / 2
    | 1 => 944315397604541 / 4000000000000
    | 2 => 305372197401053 / 800000000000
    | 3 => 275548877864887 / 4000000000000
    | 4 => 740163045100939 / 4000000000000
    | 5 => 2009686649666463 / 4000000000000
    | 6 => 1480326090202519 / 4000000000000
    | 7 => 2536563986911987 / 4000000000000
    | 8 => 1868421552143833 / 4000000000000
    | 9 => 2866639147154359 / 4000000000000
    | 10 => 1655054883278911 / 4000000000000
    | 11 => 2936923933817099 / 4000000000000
    | 12 => 2744055306724631 / 4000000000000
    | 13 => 1958287346977223 / 4000000000000
    | 14 => 2220489135302817 / 4000000000000
    | 15 => 1851212343385873 / 4000000000000
    | 16 => 1635602247019333 / 4000000000000
    | 17 => 474061281845967 / 800000000000
    | 18 => 1311278454064349 / 4000000000000
    | 19 => 1111585267521589 / 4000000000000
    | 20 => 695578447856167 / 4000000000000
    | 21 => 374084402646489 / 4000000000000
    | 22 => 1015711922966467 / 4000000000000
    | 23 => 1386867794927459 / 4000000000000
    | 24 => 586421552143833 / 4000000000000
    | 25 => 2383771052313593 / 4000000000000
    | _ => 1592248589308087 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))
    | 1 => (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))
    | 2 => (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000))
    | 3 => (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))
    | 4 => (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))
    | 5 => (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000))
    | 6 => (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))
    | 7 => (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))
    | 8 => (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000))
    | 9 => (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))
    | 10 => (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))
    | 11 => (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000))
    | 12 => (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))
    | 13 => (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))
    | 14 => (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000))
    | 15 => (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))
    | 16 => (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))
    | 17 => (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000))
    | 18 => (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))
    | 19 => (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))
    | 20 => (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000))
    | 21 => (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))
    | 22 => (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))
    | 23 => (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000))
    | 24 => (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))
    | 25 => (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))
    | _ => (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11051046431 / 1000000000000) (11051047528 / 1000000000000)
      | 1 => orderedInterval (-2850016015 / 1000000000000) (-2850015976 / 1000000000000)
      | 2 => orderedInterval (-128385253 / 1000000000000) (-128385234 / 1000000000000)
      | 3 => orderedInterval (-5755337921 / 1000000000000) (-5755337792 / 1000000000000)
      | 4 => orderedInterval (363845225 / 1000000000000) (363846333 / 1000000000000)
      | 5 => orderedInterval (-2255588260 / 1000000000000) (-2255588176 / 1000000000000)
      | 6 => orderedInterval (-10739452614 / 1000000000000) (-10739445321 / 1000000000000)
      | 7 => orderedInterval (-2891152055 / 1000000000000) (-2891151133 / 1000000000000)
      | _ => orderedInterval (-443824478 / 1000000000000) (-443824386 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13666806075 / 1000000000000) (13666807380 / 1000000000000)
      | 1 => orderedInterval (-4665288839 / 1000000000000) (-4665288794 / 1000000000000)
      | 2 => orderedInterval (-3105183708 / 1000000000000) (-3105183676 / 1000000000000)
      | 3 => orderedInterval (8539444987 / 1000000000000) (8539445254 / 1000000000000)
      | 4 => orderedInterval (5730730149 / 1000000000000) (5730732501 / 1000000000000)
      | 5 => orderedInterval (-2131061024 / 1000000000000) (-2131060902 / 1000000000000)
      | 6 => orderedInterval (3962188709 / 1000000000000) (3962195164 / 1000000000000)
      | 7 => orderedInterval (1672237773 / 1000000000000) (1672238762 / 1000000000000)
      | _ => orderedInterval (4187938909 / 1000000000000) (4187939037 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10602339945 / 1000000000000) (-10602338388 / 1000000000000)
      | 1 => orderedInterval (3625155050 / 1000000000000) (3625155111 / 1000000000000)
      | 2 => orderedInterval (840343804 / 1000000000000) (840343861 / 1000000000000)
      | 3 => orderedInterval (27505387184 / 1000000000000) (27505387756 / 1000000000000)
      | 4 => orderedInterval (307400328 / 1000000000000) (307405338 / 1000000000000)
      | 5 => orderedInterval (3285832627 / 1000000000000) (3285832806 / 1000000000000)
      | 6 => orderedInterval (9183190788 / 1000000000000) (9183196557 / 1000000000000)
      | 7 => orderedInterval (3432287069 / 1000000000000) (3432288140 / 1000000000000)
      | _ => orderedInterval (-75015403 / 1000000000000) (-75015216 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14540815946 / 1000000000000) (-14540814092 / 1000000000000)
      | 1 => orderedInterval (8659593890 / 1000000000000) (8659593981 / 1000000000000)
      | 2 => orderedInterval (9874168879 / 1000000000000) (9874168982 / 1000000000000)
      | 3 => orderedInterval (-32763182228 / 1000000000000) (-32763180973 / 1000000000000)
      | 4 => orderedInterval (-14504845989 / 1000000000000) (-14504835310 / 1000000000000)
      | 5 => orderedInterval (5962107499 / 1000000000000) (5962107765 / 1000000000000)
      | 6 => orderedInterval (-3498576180 / 1000000000000) (-3498571012 / 1000000000000)
      | 7 => orderedInterval (-1975528204 / 1000000000000) (-1975527048 / 1000000000000)
      | _ => orderedInterval (2636217607 / 1000000000000) (2636217895 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9769732364 / 1000000000000) (9769734576 / 1000000000000)
      | 1 => orderedInterval (-8176720338 / 1000000000000) (-8176720198 / 1000000000000)
      | 2 => orderedInterval (-4010303348 / 1000000000000) (-4010303159 / 1000000000000)
      | 3 => orderedInterval (-135813392554 / 1000000000000) (-135813389772 / 1000000000000)
      | 4 => orderedInterval (-6020576845 / 1000000000000) (-6020554027 / 1000000000000)
      | 5 => orderedInterval (-3777927299 / 1000000000000) (-3777926895 / 1000000000000)
      | 6 => orderedInterval (-8707556154 / 1000000000000) (-8707551482 / 1000000000000)
      | 7 => orderedInterval (-4095871577 / 1000000000000) (-4095870325 / 1000000000000)
      | _ => orderedInterval (3110823248 / 1000000000000) (3110823708 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13648864940 / 1000000000000) (-13648854157 / 1000000000000)
    | 1 => orderedInterval (27857813031 / 1000000000000) (27857824726 / 1000000000000)
    | 2 => orderedInterval (37502241502 / 1000000000000) (37502255965 / 1000000000000)
    | 3 => orderedInterval (-40150860672 / 1000000000000) (-40150839812 / 1000000000000)
    | _ => orderedInterval (-157721792503 / 1000000000000) (-157721757574 / 1000000000000)

theorem compactCertificate449_stateChecks0 :
    compactCertificate449.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (641 / 2)) (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (944315397604541 / 4000000000000)) (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (305372197401053 / 800000000000)) (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks1 :
    compactCertificate449.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (275548877864887 / 4000000000000)) (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (740163045100939 / 4000000000000)) (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2009686649666463 / 4000000000000)) (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks2 :
    compactCertificate449.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1480326090202519 / 4000000000000)) (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2536563986911987 / 4000000000000)) (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1868421552143833 / 4000000000000)) (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks3 :
    compactCertificate449.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2866639147154359 / 4000000000000)) (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1655054883278911 / 4000000000000)) (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2936923933817099 / 4000000000000)) (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks4 :
    compactCertificate449.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2744055306724631 / 4000000000000)) (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1958287346977223 / 4000000000000)) (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2220489135302817 / 4000000000000)) (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks5 :
    compactCertificate449.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1851212343385873 / 4000000000000)) (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1635602247019333 / 4000000000000)) (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (474061281845967 / 800000000000)) (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks6 :
    compactCertificate449.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1311278454064349 / 4000000000000)) (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1111585267521589 / 4000000000000)) (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (695578447856167 / 4000000000000)) (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks7 :
    compactCertificate449.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (374084402646489 / 4000000000000)) (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1015711922966467 / 4000000000000)) (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1386867794927459 / 4000000000000)) (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_stateChecks8 :
    compactCertificate449.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (586421552143833 / 4000000000000)) (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2383771052313593 / 4000000000000)) (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1592248589308087 / 4000000000000)) (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_states : ∀ j,
    BesselStateValid (compactCertificate449.point j) (compactCertificate449.state j) :=
  compactCertificate449.statesValid_of_checks3 compactCertificate449_stateChecks0
    compactCertificate449_stateChecks1 compactCertificate449_stateChecks2
    compactCertificate449_stateChecks3 compactCertificate449_stateChecks4
    compactCertificate449_stateChecks5 compactCertificate449_stateChecks6
    compactCertificate449_stateChecks7 compactCertificate449_stateChecks8

theorem compactCertificate449_chunkChecks0_0 :
    compactCertificate449.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (641 / 2) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (944315397604541 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (305372197401053 / 800000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000)))) (orderedInterval (11051046431 / 1000000000000) (11051047528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (275548877864887 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (740163045100939 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2009686649666463 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000)))) (orderedInterval (-2850016015 / 1000000000000) (-2850015976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1480326090202519 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2536563986911987 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1868421552143833 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000)))) (orderedInterval (-128385253 / 1000000000000) (-128385234 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks0_1 :
    compactCertificate449.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2866639147154359 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1655054883278911 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2936923933817099 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000)))) (orderedInterval (-5755337921 / 1000000000000) (-5755337792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2744055306724631 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1958287346977223 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2220489135302817 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000)))) (orderedInterval (363845225 / 1000000000000) (363846333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1851212343385873 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1635602247019333 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (474061281845967 / 800000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000)))) (orderedInterval (-2255588260 / 1000000000000) (-2255588176 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks0_2 :
    compactCertificate449.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1311278454064349 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1111585267521589 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (695578447856167 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000)))) (orderedInterval (-10739452614 / 1000000000000) (-10739445321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (374084402646489 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1015711922966467 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1386867794927459 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000)))) (orderedInterval (-2891152055 / 1000000000000) (-2891151133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (586421552143833 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2383771052313593 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1592248589308087 / 4000000000000) 0 (IntervalRat.scale (641 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000)))) (orderedInterval (-443824478 / 1000000000000) (-443824386 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks0 :
    compactCertificate449.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate449.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate449_chunkChecks0_0
    compactCertificate449_chunkChecks0_1 compactCertificate449_chunkChecks0_2

theorem compactCertificate449_chunkChecks1_0 :
    compactCertificate449.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (641 / 2) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (944315397604541 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (305372197401053 / 800000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000)))) (orderedInterval (13666806075 / 1000000000000) (13666807380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (275548877864887 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (740163045100939 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2009686649666463 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000)))) (orderedInterval (-4665288839 / 1000000000000) (-4665288794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1480326090202519 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2536563986911987 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1868421552143833 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000)))) (orderedInterval (-3105183708 / 1000000000000) (-3105183676 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks1_1 :
    compactCertificate449.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2866639147154359 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1655054883278911 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2936923933817099 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000)))) (orderedInterval (8539444987 / 1000000000000) (8539445254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2744055306724631 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1958287346977223 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2220489135302817 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000)))) (orderedInterval (5730730149 / 1000000000000) (5730732501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1851212343385873 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1635602247019333 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (474061281845967 / 800000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000)))) (orderedInterval (-2131061024 / 1000000000000) (-2131060902 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks1_2 :
    compactCertificate449.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1311278454064349 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1111585267521589 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (695578447856167 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000)))) (orderedInterval (3962188709 / 1000000000000) (3962195164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (374084402646489 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1015711922966467 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1386867794927459 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000)))) (orderedInterval (1672237773 / 1000000000000) (1672238762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (586421552143833 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2383771052313593 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1592248589308087 / 4000000000000) 1 (IntervalRat.scale (641 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000)))) (orderedInterval (4187938909 / 1000000000000) (4187939037 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks1 :
    compactCertificate449.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate449.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate449_chunkChecks1_0
    compactCertificate449_chunkChecks1_1 compactCertificate449_chunkChecks1_2

theorem compactCertificate449_chunkChecks2_0 :
    compactCertificate449.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (641 / 2) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (944315397604541 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (305372197401053 / 800000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000)))) (orderedInterval (-10602339945 / 1000000000000) (-10602338388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (275548877864887 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (740163045100939 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2009686649666463 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000)))) (orderedInterval (3625155050 / 1000000000000) (3625155111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1480326090202519 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2536563986911987 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1868421552143833 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000)))) (orderedInterval (840343804 / 1000000000000) (840343861 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks2_1 :
    compactCertificate449.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2866639147154359 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1655054883278911 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2936923933817099 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000)))) (orderedInterval (27505387184 / 1000000000000) (27505387756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2744055306724631 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1958287346977223 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2220489135302817 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000)))) (orderedInterval (307400328 / 1000000000000) (307405338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1851212343385873 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1635602247019333 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (474061281845967 / 800000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000)))) (orderedInterval (3285832627 / 1000000000000) (3285832806 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks2_2 :
    compactCertificate449.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1311278454064349 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1111585267521589 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (695578447856167 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000)))) (orderedInterval (9183190788 / 1000000000000) (9183196557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (374084402646489 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1015711922966467 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1386867794927459 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000)))) (orderedInterval (3432287069 / 1000000000000) (3432288140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (586421552143833 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2383771052313593 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1592248589308087 / 4000000000000) 2 (IntervalRat.scale (641 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000)))) (orderedInterval (-75015403 / 1000000000000) (-75015216 / 1000000000000))) = true
  rfl'

theorem compactCertificate449_chunkChecks2 :
    compactCertificate449.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate449.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate449_chunkChecks2_0
    compactCertificate449_chunkChecks2_1 compactCertificate449_chunkChecks2_2

theorem compactCertificate449_chunkChecks3_0 :
    compactCertificate449.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (641 / 2) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (944315397604541 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (305372197401053 / 800000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000)))) (orderedInterval (-14540815946 / 1000000000000) (-14540814092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (275548877864887 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (740163045100939 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2009686649666463 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000)))) (orderedInterval (8659593890 / 1000000000000) (8659593981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1480326090202519 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2536563986911987 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1868421552143833 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000)))) (orderedInterval (9874168879 / 1000000000000) (9874168982 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate449_chunkChecks3_1 :
    compactCertificate449.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2866639147154359 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1655054883278911 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2936923933817099 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000)))) (orderedInterval (-32763182228 / 1000000000000) (-32763180973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2744055306724631 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1958287346977223 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2220489135302817 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000)))) (orderedInterval (-14504845989 / 1000000000000) (-14504835310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1851212343385873 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1635602247019333 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (474061281845967 / 800000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000)))) (orderedInterval (5962107499 / 1000000000000) (5962107765 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate449_chunkChecks3_2 :
    compactCertificate449.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1311278454064349 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1111585267521589 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (695578447856167 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000)))) (orderedInterval (-3498576180 / 1000000000000) (-3498571012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (374084402646489 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1015711922966467 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1386867794927459 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000)))) (orderedInterval (-1975528204 / 1000000000000) (-1975527048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (586421552143833 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2383771052313593 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1592248589308087 / 4000000000000) 3 (IntervalRat.scale (641 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000)))) (orderedInterval (2636217607 / 1000000000000) (2636217895 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate449_chunkChecks3 :
    compactCertificate449.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate449.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate449_chunkChecks3_0
    compactCertificate449_chunkChecks3_1 compactCertificate449_chunkChecks3_2

theorem compactCertificate449_chunkChecks4_0 :
    compactCertificate449.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (641 / 2) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33263426463 / 1000000000000) (33263426464 / 1000000000000), orderedInterval (29610833334 / 1000000000000) (29610833335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (944315397604541 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49185294852 / 1000000000000) (-49185294851 / 1000000000000), orderedInterval (-16552431647 / 1000000000000) (-16552431646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (305372197401053 / 800000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28545795564 / 1000000000000) (-28545777263 / 1000000000000), orderedInterval (29242265448 / 1000000000000) (29242283749 / 1000000000000)))) (orderedInterval (9769732364 / 1000000000000) (9769734576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (275548877864887 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (50718246093 / 1000000000000) (50718246094 / 1000000000000), orderedInterval (81297346484 / 1000000000000) (81297346485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (740163045100939 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26643397015 / 1000000000000) (-26643397014 / 1000000000000), orderedInterval (-52182831834 / 1000000000000) (-52182831833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2009686649666463 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18666039406 / 1000000000000) (18666039407 / 1000000000000), orderedInterval (30291188229 / 1000000000000) (30291188230 / 1000000000000)))) (orderedInterval (-8176720338 / 1000000000000) (-8176720198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1480326090202519 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6552505423 / 1000000000000) (6552505424 / 1000000000000), orderedInterval (40945770003 / 1000000000000) (40945770004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2536563986911987 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10101582087 / 1000000000000) (10101582088 / 1000000000000), orderedInterval (30023138428 / 1000000000000) (30023138429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1868421552143833 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7579764963 / 1000000000000) (7579764972 / 1000000000000), orderedInterval (-36139150273 / 1000000000000) (-36139150263 / 1000000000000)))) (orderedInterval (-4010303348 / 1000000000000) (-4010303159 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate449_chunkChecks4_1 :
    compactCertificate449.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2866639147154359 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27347355171 / 1000000000000) (27347355178 / 1000000000000), orderedInterval (11831540674 / 1000000000000) (11831540682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1655054883278911 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5528480664 / 1000000000000) (-5528480658 / 1000000000000), orderedInterval (38840223131 / 1000000000000) (38840223136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2936923933817099 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3421793524 / 1000000000000) (-3421793523 / 1000000000000), orderedInterval (29248664310 / 1000000000000) (29248664311 / 1000000000000)))) (orderedInterval (-135813392554 / 1000000000000) (-135813389772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2744055306724631 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28498993346 / 1000000000000) (28499052592 / 1000000000000), orderedInterval (-10782023483 / 1000000000000) (-10781964237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1958287346977223 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9567217750 / 1000000000000) (9567217751 / 1000000000000), orderedInterval (34758450279 / 1000000000000) (34758450280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2220489135302817 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5209375064 / 1000000000000) (5209375067 / 1000000000000), orderedInterval (-33466204754 / 1000000000000) (-33466204751 / 1000000000000)))) (orderedInterval (-6020576845 / 1000000000000) (-6020554027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1851212343385873 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36324919274 / 1000000000000) (-36324914870 / 1000000000000), orderedInterval (7527459522 / 1000000000000) (7527463925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1635602247019333 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37785269458 / 1000000000000) (37785269462 / 1000000000000), orderedInterval (11319469676 / 1000000000000) (11319469680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (474061281845967 / 800000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12740430578 / 1000000000000) (12740430644 / 1000000000000), orderedInterval (-30210196235 / 1000000000000) (-30210196170 / 1000000000000)))) (orderedInterval (-3777927299 / 1000000000000) (-3777926895 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate449_chunkChecks4_2 :
    compactCertificate449.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1311278454064349 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41991491579 / 1000000000000) (41991498034 / 1000000000000), orderedInterval (-13431714427 / 1000000000000) (-13431707972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1111585267521589 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38093624868 / 1000000000000) (38093732190 / 1000000000000), orderedInterval (-29046584525 / 1000000000000) (-29046477204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (695578447856167 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57416995351 / 1000000000000) (-57416992109 / 1000000000000), orderedInterval (19249856704 / 1000000000000) (19249859946 / 1000000000000)))) (orderedInterval (-8707556154 / 1000000000000) (-8707551482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (374084402646489 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4731782445 / 1000000000000) (4731782448 / 1000000000000), orderedInterval (82345439450 / 1000000000000) (82345439453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1015711922966467 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12090655019 / 1000000000000) (-12090655018 / 1000000000000), orderedInterval (-48565371387 / 1000000000000) (-48565371386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1386867794927459 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40163395654 / 1000000000000) (40163407167 / 1000000000000), orderedInterval (-14992334819 / 1000000000000) (-14992323307 / 1000000000000)))) (orderedInterval (-4095871577 / 1000000000000) (-4095870325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (586421552143833 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17253946910 / 1000000000000) (17253947141 / 1000000000000), orderedInterval (-63657010563 / 1000000000000) (-63657010332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2383771052313593 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5679404776 / 1000000000000) (-5679404774 / 1000000000000), orderedInterval (32191738899 / 1000000000000) (32191738902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1592248589308087 / 4000000000000) 4 (IntervalRat.scale (641 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5383836394 / 1000000000000) (5383836399 / 1000000000000), orderedInterval (-39633937058 / 1000000000000) (-39633937053 / 1000000000000)))) (orderedInterval (3110823248 / 1000000000000) (3110823708 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate449_chunkChecks4 :
    compactCertificate449.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate449.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate449_chunkChecks4_0
    compactCertificate449_chunkChecks4_1 compactCertificate449_chunkChecks4_2

theorem compactCertificate449_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate449.chunkCheck r b = true :=
  compactCertificate449.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate449_chunkChecks0
    · exact compactCertificate449_chunkChecks1
    · exact compactCertificate449_chunkChecks2
    · exact compactCertificate449_chunkChecks3
    · exact compactCertificate449_chunkChecks4)

theorem compactCertificate449_coefficient0 :
    compactCertificate449.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate449_coefficient1 :
    compactCertificate449.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate449_coefficient2 :
    compactCertificate449.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate449_coefficient3 :
    compactCertificate449.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate449_coefficient4 :
    compactCertificate449.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate449_coefficients : ∀ r : Fin 5,
    compactCertificate449.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate449_coefficient0
  · exact compactCertificate449_coefficient1
  · exact compactCertificate449_coefficient2
  · exact compactCertificate449_coefficient3
  · exact compactCertificate449_coefficient4

theorem compactCertificate449_lower : (1 : ℚ) ≤ compactCertificate449.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate449, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate449_proves {t : ℝ} (ht : t ∈ compactCertificate449.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate449.proves compactCertificate449_states compactCertificate449_chunks
    compactCertificate449_coefficients compactCertificate449_lower ht

end Erdos232
