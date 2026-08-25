/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate596 : CompactCertificate where
  left := 467
  right := 468
  center := 935 / 2
  grid := fun i =>
    match i.val with
    | 0 => 149
    | 1 => 110
    | 2 => 177
    | 3 => 32
    | 4 => 86
    | 5 => 233
    | 6 => 172
    | 7 => 295
    | 8 => 217
    | 9 => 333
    | 10 => 192
    | 11 => 341
    | 12 => 319
    | 13 => 227
    | 14 => 258
    | 15 => 215
    | 16 => 190
    | 17 => 275
    | 18 => 152
    | 19 => 129
    | 20 => 81
    | 21 => 43
    | 22 => 118
    | 23 => 161
    | 24 => 68
    | 25 => 277
    | _ => 185
  point := fun i =>
    match i.val with
    | 0 => 935 / 2
    | 1 => 275486707257487 / 800000000000
    | 2 => 89086740895471 / 160000000000
    | 3 => 80386334104109 / 800000000000
    | 4 => 215929000676873 / 800000000000
    | 5 => 586289241010341 / 800000000000
    | 6 => 431858001353933 / 800000000000
    | 7 => 739996046103809 / 800000000000
    | 8 => 545077738300931 / 800000000000
    | 9 => 836289423584813 / 800000000000
    | 10 => 482831923827077 / 800000000000
    | 11 => 856793721721993 / 800000000000
    | 12 => 800527835191117 / 800000000000
    | 13 => 571294436637661 / 800000000000
    | 14 => 647787002030619 / 800000000000
    | 15 => 540057267103211 / 800000000000
    | 16 => 477156973779431 / 800000000000
    | 17 => 138298689087669 / 160000000000
    | 18 => 382541452277743 / 800000000000
    | 19 => 324284625626423 / 800000000000
    | 20 => 202922261699069 / 800000000000
    | 21 => 109132267230723 / 800000000000
    | 22 => 296315334781169 / 800000000000
    | 23 => 404593256866513 / 800000000000
    | 24 => 171077738300931 / 800000000000
    | 25 => 695421508241251 / 800000000000
    | _ => 464509338846509 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))
    | 1 => (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))
    | 2 => (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000))
    | 3 => (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))
    | 4 => (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))
    | 5 => (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000))
    | 6 => (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))
    | 7 => (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))
    | 8 => (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000))
    | 9 => (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))
    | 10 => (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))
    | 11 => (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000))
    | 12 => (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))
    | 13 => (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))
    | 14 => (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000))
    | 15 => (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))
    | 16 => (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))
    | 17 => (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000))
    | 18 => (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))
    | 19 => (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))
    | 20 => (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000))
    | 21 => (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))
    | 22 => (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))
    | 23 => (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000))
    | 24 => (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))
    | 25 => (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))
    | _ => (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4879978071 / 1000000000000) (-4879978010 / 1000000000000)
      | 1 => orderedInterval (2387772570 / 1000000000000) (2387773007 / 1000000000000)
      | 2 => orderedInterval (-968562922 / 1000000000000) (-968562580 / 1000000000000)
      | 3 => orderedInterval (526953577 / 1000000000000) (526953763 / 1000000000000)
      | 4 => orderedInterval (-3071694543 / 1000000000000) (-3071693143 / 1000000000000)
      | 5 => orderedInterval (-1397610866 / 1000000000000) (-1397610819 / 1000000000000)
      | 6 => orderedInterval (-4010931543 / 1000000000000) (-4010931412 / 1000000000000)
      | 7 => orderedInterval (2468433539 / 1000000000000) (2468434046 / 1000000000000)
      | _ => orderedInterval (1328095858 / 1000000000000) (1328095988 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14226985485 / 1000000000000) (-14226985417 / 1000000000000)
      | 1 => orderedInterval (470229658 / 1000000000000) (470230319 / 1000000000000)
      | 2 => orderedInterval (-108659342 / 1000000000000) (-108658672 / 1000000000000)
      | 3 => orderedInterval (4114296242 / 1000000000000) (4114296626 / 1000000000000)
      | 4 => orderedInterval (1306863155 / 1000000000000) (1306865303 / 1000000000000)
      | 5 => orderedInterval (-3173382313 / 1000000000000) (-3173382245 / 1000000000000)
      | 6 => orderedInterval (-413212729 / 1000000000000) (-413212607 / 1000000000000)
      | 7 => orderedInterval (1335348285 / 1000000000000) (1335348467 / 1000000000000)
      | _ => orderedInterval (11641727722 / 1000000000000) (11641727905 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5662801837 / 1000000000000) (5662801913 / 1000000000000)
      | 1 => orderedInterval (-5397886787 / 1000000000000) (-5397885763 / 1000000000000)
      | 2 => orderedInterval (3268591776 / 1000000000000) (3268593093 / 1000000000000)
      | 3 => orderedInterval (5050489808 / 1000000000000) (5050490633 / 1000000000000)
      | 4 => orderedInterval (7840684386 / 1000000000000) (7840687690 / 1000000000000)
      | 5 => orderedInterval (3513012142 / 1000000000000) (3513012244 / 1000000000000)
      | 6 => orderedInterval (4742451871 / 1000000000000) (4742451988 / 1000000000000)
      | 7 => orderedInterval (-1949674882 / 1000000000000) (-1949674793 / 1000000000000)
      | _ => orderedInterval (-1035703092 / 1000000000000) (-1035702823 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14391358832 / 1000000000000) (14391358921 / 1000000000000)
      | 1 => orderedInterval (411797731 / 1000000000000) (411799331 / 1000000000000)
      | 2 => orderedInterval (-1351781209 / 1000000000000) (-1351778617 / 1000000000000)
      | 3 => orderedInterval (-14525001810 / 1000000000000) (-14525000003 / 1000000000000)
      | 4 => orderedInterval (-4546050072 / 1000000000000) (-4546044983 / 1000000000000)
      | 5 => orderedInterval (6174324104 / 1000000000000) (6174324261 / 1000000000000)
      | 6 => orderedInterval (123424895 / 1000000000000) (123425009 / 1000000000000)
      | 7 => orderedInterval (-2125357981 / 1000000000000) (-2125357917 / 1000000000000)
      | _ => orderedInterval (-25593772114 / 1000000000000) (-25593771699 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-6828339404 / 1000000000000) (-6828339300 / 1000000000000)
      | 1 => orderedInterval (12702261798 / 1000000000000) (12702264304 / 1000000000000)
      | 2 => orderedInterval (-11677560215 / 1000000000000) (-11677555100 / 1000000000000)
      | 3 => orderedInterval (-39519396287 / 1000000000000) (-39519392274 / 1000000000000)
      | 4 => orderedInterval (-21381763373 / 1000000000000) (-21381755502 / 1000000000000)
      | 5 => orderedInterval (-9855662714 / 1000000000000) (-9855662463 / 1000000000000)
      | 6 => orderedInterval (-5353580771 / 1000000000000) (-5353580658 / 1000000000000)
      | 7 => orderedInterval (2332941018 / 1000000000000) (2332941076 / 1000000000000)
      | _ => orderedInterval (-718177308 / 1000000000000) (-718176642 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7617522401 / 1000000000000) (-7617519160 / 1000000000000)
    | 1 => orderedInterval (946225193 / 1000000000000) (946229679 / 1000000000000)
    | 2 => orderedInterval (21694767059 / 1000000000000) (21694774182 / 1000000000000)
    | 3 => orderedInterval (-27041057624 / 1000000000000) (-27041045697 / 1000000000000)
    | _ => orderedInterval (-80299277256 / 1000000000000) (-80299256559 / 1000000000000)

theorem compactCertificate596_stateChecks0 :
    compactCertificate596.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (935 / 2)) (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (275486707257487 / 800000000000)) (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (89086740895471 / 160000000000)) (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks1 :
    compactCertificate596.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (80386334104109 / 800000000000)) (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (215929000676873 / 800000000000)) (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (586289241010341 / 800000000000)) (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks2 :
    compactCertificate596.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (431858001353933 / 800000000000)) (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (739996046103809 / 800000000000)) (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (545077738300931 / 800000000000)) (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks3 :
    compactCertificate596.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 333 12 (836289423584813 / 800000000000)) (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (482831923827077 / 800000000000)) (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 341 12 (856793721721993 / 800000000000)) (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks4 :
    compactCertificate596.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 319 12 (800527835191117 / 800000000000)) (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (571294436637661 / 800000000000)) (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (647787002030619 / 800000000000)) (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks5 :
    compactCertificate596.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (540057267103211 / 800000000000)) (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (477156973779431 / 800000000000)) (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (138298689087669 / 160000000000)) (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks6 :
    compactCertificate596.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (382541452277743 / 800000000000)) (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (324284625626423 / 800000000000)) (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (202922261699069 / 800000000000)) (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks7 :
    compactCertificate596.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (109132267230723 / 800000000000)) (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (296315334781169 / 800000000000)) (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (404593256866513 / 800000000000)) (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_stateChecks8 :
    compactCertificate596.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (171077738300931 / 800000000000)) (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (695421508241251 / 800000000000)) (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (464509338846509 / 800000000000)) (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_states : ∀ j,
    BesselStateValid (compactCertificate596.point j) (compactCertificate596.state j) :=
  compactCertificate596.statesValid_of_checks3 compactCertificate596_stateChecks0
    compactCertificate596_stateChecks1 compactCertificate596_stateChecks2
    compactCertificate596_stateChecks3 compactCertificate596_stateChecks4
    compactCertificate596_stateChecks5 compactCertificate596_stateChecks6
    compactCertificate596_stateChecks7 compactCertificate596_stateChecks8

theorem compactCertificate596_chunkChecks0_0 :
    compactCertificate596.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (935 / 2) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (275486707257487 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (89086740895471 / 160000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000)))) (orderedInterval (-4879978071 / 1000000000000) (-4879978010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (80386334104109 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (215929000676873 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (586289241010341 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000)))) (orderedInterval (2387772570 / 1000000000000) (2387773007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (431858001353933 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (739996046103809 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (545077738300931 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000)))) (orderedInterval (-968562922 / 1000000000000) (-968562580 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks0_1 :
    compactCertificate596.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (836289423584813 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (482831923827077 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (856793721721993 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000)))) (orderedInterval (526953577 / 1000000000000) (526953763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (800527835191117 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (571294436637661 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (647787002030619 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000)))) (orderedInterval (-3071694543 / 1000000000000) (-3071693143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (540057267103211 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (477156973779431 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (138298689087669 / 160000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000)))) (orderedInterval (-1397610866 / 1000000000000) (-1397610819 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks0_2 :
    compactCertificate596.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (382541452277743 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (324284625626423 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (202922261699069 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000)))) (orderedInterval (-4010931543 / 1000000000000) (-4010931412 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (109132267230723 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (296315334781169 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (404593256866513 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000)))) (orderedInterval (2468433539 / 1000000000000) (2468434046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (171077738300931 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (695421508241251 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (464509338846509 / 800000000000) 0 (IntervalRat.scale (935 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000)))) (orderedInterval (1328095858 / 1000000000000) (1328095988 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks0 :
    compactCertificate596.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate596.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate596_chunkChecks0_0
    compactCertificate596_chunkChecks0_1 compactCertificate596_chunkChecks0_2

theorem compactCertificate596_chunkChecks1_0 :
    compactCertificate596.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (935 / 2) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (275486707257487 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (89086740895471 / 160000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000)))) (orderedInterval (-14226985485 / 1000000000000) (-14226985417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (80386334104109 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (215929000676873 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (586289241010341 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000)))) (orderedInterval (470229658 / 1000000000000) (470230319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (431858001353933 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (739996046103809 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (545077738300931 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000)))) (orderedInterval (-108659342 / 1000000000000) (-108658672 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks1_1 :
    compactCertificate596.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (836289423584813 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (482831923827077 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (856793721721993 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000)))) (orderedInterval (4114296242 / 1000000000000) (4114296626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (800527835191117 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (571294436637661 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (647787002030619 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000)))) (orderedInterval (1306863155 / 1000000000000) (1306865303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (540057267103211 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (477156973779431 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (138298689087669 / 160000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000)))) (orderedInterval (-3173382313 / 1000000000000) (-3173382245 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks1_2 :
    compactCertificate596.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (382541452277743 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (324284625626423 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (202922261699069 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000)))) (orderedInterval (-413212729 / 1000000000000) (-413212607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (109132267230723 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (296315334781169 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (404593256866513 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000)))) (orderedInterval (1335348285 / 1000000000000) (1335348467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (171077738300931 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (695421508241251 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (464509338846509 / 800000000000) 1 (IntervalRat.scale (935 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000)))) (orderedInterval (11641727722 / 1000000000000) (11641727905 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks1 :
    compactCertificate596.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate596.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate596_chunkChecks1_0
    compactCertificate596_chunkChecks1_1 compactCertificate596_chunkChecks1_2

theorem compactCertificate596_chunkChecks2_0 :
    compactCertificate596.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (935 / 2) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (275486707257487 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (89086740895471 / 160000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000)))) (orderedInterval (5662801837 / 1000000000000) (5662801913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (80386334104109 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (215929000676873 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (586289241010341 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000)))) (orderedInterval (-5397886787 / 1000000000000) (-5397885763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (431858001353933 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (739996046103809 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (545077738300931 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000)))) (orderedInterval (3268591776 / 1000000000000) (3268593093 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks2_1 :
    compactCertificate596.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (836289423584813 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (482831923827077 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (856793721721993 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000)))) (orderedInterval (5050489808 / 1000000000000) (5050490633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (800527835191117 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (571294436637661 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (647787002030619 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000)))) (orderedInterval (7840684386 / 1000000000000) (7840687690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (540057267103211 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (477156973779431 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (138298689087669 / 160000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000)))) (orderedInterval (3513012142 / 1000000000000) (3513012244 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks2_2 :
    compactCertificate596.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (382541452277743 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (324284625626423 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (202922261699069 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000)))) (orderedInterval (4742451871 / 1000000000000) (4742451988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (109132267230723 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (296315334781169 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (404593256866513 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000)))) (orderedInterval (-1949674882 / 1000000000000) (-1949674793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (171077738300931 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (695421508241251 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (464509338846509 / 800000000000) 2 (IntervalRat.scale (935 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000)))) (orderedInterval (-1035703092 / 1000000000000) (-1035702823 / 1000000000000))) = true
  rfl'

theorem compactCertificate596_chunkChecks2 :
    compactCertificate596.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate596.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate596_chunkChecks2_0
    compactCertificate596_chunkChecks2_1 compactCertificate596_chunkChecks2_2

theorem compactCertificate596_chunkChecks3_0 :
    compactCertificate596.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (935 / 2) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (275486707257487 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (89086740895471 / 160000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000)))) (orderedInterval (14391358832 / 1000000000000) (14391358921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (80386334104109 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (215929000676873 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (586289241010341 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000)))) (orderedInterval (411797731 / 1000000000000) (411799331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (431858001353933 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (739996046103809 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (545077738300931 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000)))) (orderedInterval (-1351781209 / 1000000000000) (-1351778617 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate596_chunkChecks3_1 :
    compactCertificate596.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (836289423584813 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (482831923827077 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (856793721721993 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000)))) (orderedInterval (-14525001810 / 1000000000000) (-14525000003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (800527835191117 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (571294436637661 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (647787002030619 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000)))) (orderedInterval (-4546050072 / 1000000000000) (-4546044983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (540057267103211 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (477156973779431 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (138298689087669 / 160000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000)))) (orderedInterval (6174324104 / 1000000000000) (6174324261 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate596_chunkChecks3_2 :
    compactCertificate596.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (382541452277743 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (324284625626423 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (202922261699069 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000)))) (orderedInterval (123424895 / 1000000000000) (123425009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (109132267230723 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (296315334781169 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (404593256866513 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000)))) (orderedInterval (-2125357981 / 1000000000000) (-2125357917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (171077738300931 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (695421508241251 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (464509338846509 / 800000000000) 3 (IntervalRat.scale (935 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000)))) (orderedInterval (-25593772114 / 1000000000000) (-25593771699 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate596_chunkChecks3 :
    compactCertificate596.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate596.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate596_chunkChecks3_0
    compactCertificate596_chunkChecks3_1 compactCertificate596_chunkChecks3_2

theorem compactCertificate596_chunkChecks4_0 :
    compactCertificate596.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (935 / 2) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6890439233 / 1000000000000) (-6890439232 / 1000000000000), orderedInterval (-36245576580 / 1000000000000) (-36245576579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (275486707257487 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17993294815 / 1000000000000) (-17993294268 / 1000000000000), orderedInterval (39076803786 / 1000000000000) (39076804333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (89086740895471 / 160000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33761896162 / 1000000000000) (-33761895785 / 1000000000000), orderedInterval (-1841728342 / 1000000000000) (-1841727965 / 1000000000000)))) (orderedInterval (-6828339404 / 1000000000000) (-6828339300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (80386334104109 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53441385812 / 1000000000000) (53441385813 / 1000000000000), orderedInterval (58722455459 / 1000000000000) (58722455460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (215929000676873 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24098327449 / 1000000000000) (24098327450 / 1000000000000), orderedInterval (42120498088 / 1000000000000) (42120498089 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (586289241010341 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29367177612 / 1000000000000) (-29367172262 / 1000000000000), orderedInterval (2519144702 / 1000000000000) (2519150052 / 1000000000000)))) (orderedInterval (12702261798 / 1000000000000) (12702264304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (431858001353933 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8620242918 / 1000000000000) (8620242919 / 1000000000000), orderedInterval (33233631151 / 1000000000000) (33233631152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (739996046103809 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21925568712 / 1000000000000) (21925578933 / 1000000000000), orderedInterval (-14417079328 / 1000000000000) (-14417069107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (545077738300931 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12094091514 / 1000000000000) (-12094091513 / 1000000000000), orderedInterval (-28064022606 / 1000000000000) (-28064022605 / 1000000000000)))) (orderedInterval (-11677560215 / 1000000000000) (-11677555100 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate596_chunkChecks4_1 :
    compactCertificate596.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (836289423584813 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (81327490 / 1000000000000) (81327491 / 1000000000000), orderedInterval (-24677724064 / 1000000000000) (-24677724063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (482831923827077 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29501028571 / 1000000000000) (29501028574 / 1000000000000), orderedInterval (13558594350 / 1000000000000) (13558594352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (856793721721993 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11567433801 / 1000000000000) (-11567433800 / 1000000000000), orderedInterval (-21456544761 / 1000000000000) (-21456544760 / 1000000000000)))) (orderedInterval (-39519396287 / 1000000000000) (-39519392274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (800527835191117 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16688272420 / 1000000000000) (16688272744 / 1000000000000), orderedInterval (-18921339068 / 1000000000000) (-18921338745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (571294436637661 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29314989105 / 1000000000000) (-29314974950 / 1000000000000), orderedInterval (5686959520 / 1000000000000) (5686973675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (647787002030619 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-333893727 / 1000000000000) (-333893726 / 1000000000000), orderedInterval (28037635235 / 1000000000000) (28037635236 / 1000000000000)))) (orderedInterval (-21381763373 / 1000000000000) (-21381755502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (540057267103211 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12364014622 / 1000000000000) (-12364014621 / 1000000000000), orderedInterval (-28100835531 / 1000000000000) (-28100835530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (477156973779431 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10549566389 / 1000000000000) (10549566390 / 1000000000000), orderedInterval (30911405542 / 1000000000000) (30911405543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (138298689087669 / 160000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25430398590 / 1000000000000) (-25430398539 / 1000000000000), orderedInterval (-9462129373 / 1000000000000) (-9462129322 / 1000000000000)))) (orderedInterval (-9855662714 / 1000000000000) (-9855662463 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate596_chunkChecks4_2 :
    compactCertificate596.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (382541452277743 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36175342928 / 1000000000000) (36175343007 / 1000000000000), orderedInterval (4725776476 / 1000000000000) (4725776555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (324284625626423 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30428237587 / 1000000000000) (-30428237586 / 1000000000000), orderedInterval (-25352291128 / 1000000000000) (-25352291127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (202922261699069 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1566429632 / 1000000000000) (1566429636 / 1000000000000), orderedInterval (-50076620484 / 1000000000000) (-50076620481 / 1000000000000)))) (orderedInterval (-5353580771 / 1000000000000) (-5353580658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (109132267230723 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58574341526 / 1000000000000) (-58574317115 / 1000000000000), orderedInterval (35368748933 / 1000000000000) (35368773343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (296315334781169 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18823624861 / 1000000000000) (18823624862 / 1000000000000), orderedInterval (36912849271 / 1000000000000) (36912849272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (404593256866513 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-23668158575 / 1000000000000) (-23668158574 / 1000000000000), orderedInterval (-26407701145 / 1000000000000) (-26407701144 / 1000000000000)))) (orderedInterval (2332941018 / 1000000000000) (2332941076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (171077738300931 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46020420725 / 1000000000000) (46020420726 / 1000000000000), orderedInterval (29202844380 / 1000000000000) (29202844381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (695421508241251 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4285439458 / 1000000000000) (4285439459 / 1000000000000), orderedInterval (-26723069313 / 1000000000000) (-26723069312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (464509338846509 / 800000000000) 4 (IntervalRat.scale (935 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7459031205 / 1000000000000) (-7459031204 / 1000000000000), orderedInterval (-32254698427 / 1000000000000) (-32254698426 / 1000000000000)))) (orderedInterval (-718177308 / 1000000000000) (-718176642 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate596_chunkChecks4 :
    compactCertificate596.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate596.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate596_chunkChecks4_0
    compactCertificate596_chunkChecks4_1 compactCertificate596_chunkChecks4_2

theorem compactCertificate596_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate596.chunkCheck r b = true :=
  compactCertificate596.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate596_chunkChecks0
    · exact compactCertificate596_chunkChecks1
    · exact compactCertificate596_chunkChecks2
    · exact compactCertificate596_chunkChecks3
    · exact compactCertificate596_chunkChecks4)

theorem compactCertificate596_coefficient0 :
    compactCertificate596.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate596_coefficient1 :
    compactCertificate596.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate596_coefficient2 :
    compactCertificate596.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate596_coefficient3 :
    compactCertificate596.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate596_coefficient4 :
    compactCertificate596.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate596_coefficients : ∀ r : Fin 5,
    compactCertificate596.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate596_coefficient0
  · exact compactCertificate596_coefficient1
  · exact compactCertificate596_coefficient2
  · exact compactCertificate596_coefficient3
  · exact compactCertificate596_coefficient4

theorem compactCertificate596_lower : (1 : ℚ) ≤ compactCertificate596.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate596, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate596_proves {t : ℝ} (ht : t ∈ compactCertificate596.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate596.proves compactCertificate596_states compactCertificate596_chunks
    compactCertificate596_coefficients compactCertificate596_lower ht

end Erdos232
