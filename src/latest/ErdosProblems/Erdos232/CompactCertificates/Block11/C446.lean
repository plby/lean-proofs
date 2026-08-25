/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate446 : CompactCertificate where
  left := 317
  right := 318
  center := 635 / 2
  grid := fun i =>
    match i.val with
    | 0 => 101
    | 1 => 74
    | 2 => 120
    | 3 => 22
    | 4 => 58
    | 5 => 159
    | 6 => 117
    | 7 => 200
    | 8 => 147
    | 9 => 226
    | 10 => 131
    | 11 => 232
    | 12 => 216
    | 13 => 154
    | 14 => 175
    | 15 => 146
    | 16 => 129
    | 17 => 187
    | 18 => 103
    | 19 => 88
    | 20 => 55
    | 21 => 30
    | 22 => 80
    | 23 => 109
    | 24 => 46
    | 25 => 188
    | _ => 126
  point := fun i =>
    match i.val with
    | 0 => 635 / 2
    | 1 => 187095250383427 / 800000000000
    | 2 => 60502759859491 / 160000000000
    | 3 => 54593927439689 / 800000000000
    | 4 => 146646968374133 / 800000000000
    | 5 => 398175046033761 / 800000000000
    | 6 => 293293936748393 / 800000000000
    | 7 => 502564159653389 / 800000000000
    | 8 => 370186485370151 / 800000000000
    | 9 => 567961266284873 / 800000000000
    | 10 => 327912589978817 / 800000000000
    | 11 => 581886645233653 / 800000000000
    | 12 => 543673984327657 / 800000000000
    | 13 => 387991408839481 / 800000000000
    | 14 => 439940905122399 / 800000000000
    | 15 => 366776860546031 / 800000000000
    | 16 => 324058479518651 / 800000000000
    | 17 => 93924778150449 / 160000000000
    | 18 => 259800879354403 / 800000000000
    | 19 => 220236082644683 / 800000000000
    | 20 => 137813514629849 / 800000000000
    | 21 => 74116566514983 / 800000000000
    | 22 => 201240895813949 / 800000000000
    | 23 => 274777238620573 / 800000000000
    | 24 => 116186485370151 / 800000000000
    | 25 => 472291612548871 / 800000000000
    | _ => 315468909270089 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))
    | 1 => (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))
    | 2 => (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000))
    | 3 => (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))
    | 4 => (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))
    | 5 => (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000))
    | 6 => (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))
    | 7 => (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))
    | 8 => (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000))
    | 9 => (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))
    | 10 => (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))
    | 11 => (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000))
    | 12 => (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))
    | 13 => (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))
    | 14 => (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000))
    | 15 => (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))
    | 16 => (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))
    | 17 => (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000))
    | 18 => (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))
    | 19 => (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))
    | 20 => (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000))
    | 21 => (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))
    | 22 => (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))
    | 23 => (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000))
    | 24 => (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))
    | 25 => (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))
    | _ => (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12132423673 / 1000000000000) (-12132422155 / 1000000000000)
      | 1 => orderedInterval (-9898317 / 1000000000000) (-9891848 / 1000000000000)
      | 2 => orderedInterval (-1499646728 / 1000000000000) (-1499646660 / 1000000000000)
      | 3 => orderedInterval (-4066862502 / 1000000000000) (-4066859212 / 1000000000000)
      | 4 => orderedInterval (2757234109 / 1000000000000) (2757237596 / 1000000000000)
      | 5 => orderedInterval (1225515707 / 1000000000000) (1225515738 / 1000000000000)
      | 6 => orderedInterval (7064451984 / 1000000000000) (7064454204 / 1000000000000)
      | 7 => orderedInterval (3346514721 / 1000000000000) (3346516890 / 1000000000000)
      | _ => orderedInterval (4014121336 / 1000000000000) (4014123321 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11034483530 / 1000000000000) (-11034482010 / 1000000000000)
      | 1 => orderedInterval (1518625472 / 1000000000000) (1518635487 / 1000000000000)
      | 2 => orderedInterval (-1344492697 / 1000000000000) (-1344492593 / 1000000000000)
      | 3 => orderedInterval (-3895727862 / 1000000000000) (-3895723312 / 1000000000000)
      | 4 => orderedInterval (-1595202435 / 1000000000000) (-1595196925 / 1000000000000)
      | 5 => orderedInterval (1446090368 / 1000000000000) (1446090412 / 1000000000000)
      | 6 => orderedInterval (-5933677936 / 1000000000000) (-5933675676 / 1000000000000)
      | 7 => orderedInterval (-1683259274 / 1000000000000) (-1683258382 / 1000000000000)
      | _ => orderedInterval (-11324638726 / 1000000000000) (-11324636245 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11408981039 / 1000000000000) (11408982642 / 1000000000000)
      | 1 => orderedInterval (4596444029 / 1000000000000) (4596459689 / 1000000000000)
      | 2 => orderedInterval (4284088238 / 1000000000000) (4284088399 / 1000000000000)
      | 3 => orderedInterval (28480678829 / 1000000000000) (28480685405 / 1000000000000)
      | 4 => orderedInterval (-5309228643 / 1000000000000) (-5309219817 / 1000000000000)
      | 5 => orderedInterval (-1608239826 / 1000000000000) (-1608239759 / 1000000000000)
      | 6 => orderedInterval (-7463056692 / 1000000000000) (-7463054383 / 1000000000000)
      | 7 => orderedInterval (-3222856087 / 1000000000000) (-3222855545 / 1000000000000)
      | _ => orderedInterval (-3036560271 / 1000000000000) (-3036557155 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11335233632 / 1000000000000) (11335235384 / 1000000000000)
      | 1 => orderedInterval (-5100151798 / 1000000000000) (-5100127292 / 1000000000000)
      | 2 => orderedInterval (5563479208 / 1000000000000) (5563479462 / 1000000000000)
      | 3 => orderedInterval (9480832696 / 1000000000000) (9480842757 / 1000000000000)
      | 4 => orderedInterval (3030882842 / 1000000000000) (3030897167 / 1000000000000)
      | 5 => orderedInterval (47939523 / 1000000000000) (47939625 / 1000000000000)
      | 6 => orderedInterval (4806900669 / 1000000000000) (4806903024 / 1000000000000)
      | 7 => orderedInterval (1386079076 / 1000000000000) (1386079536 / 1000000000000)
      | _ => orderedInterval (25700234925 / 1000000000000) (25700238851 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10209852114 / 1000000000000) (-10209850138 / 1000000000000)
      | 1 => orderedInterval (-12736156941 / 1000000000000) (-12736118472 / 1000000000000)
      | 2 => orderedInterval (-13410478801 / 1000000000000) (-13410478390 / 1000000000000)
      | 3 => orderedInterval (-158383661671 / 1000000000000) (-158383645067 / 1000000000000)
      | 4 => orderedInterval (7106845507 / 1000000000000) (7106869236 / 1000000000000)
      | 5 => orderedInterval (1128398194 / 1000000000000) (1128398354 / 1000000000000)
      | 6 => orderedInterval (7687812863 / 1000000000000) (7687815274 / 1000000000000)
      | 7 => orderedInterval (3994793256 / 1000000000000) (3994793718 / 1000000000000)
      | _ => orderedInterval (-4484699537 / 1000000000000) (-4484694548 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (699006637 / 1000000000000) (699027874 / 1000000000000)
    | 1 => orderedInterval (-33846766620 / 1000000000000) (-33846739244 / 1000000000000)
    | 2 => orderedInterval (28130250616 / 1000000000000) (28130289476 / 1000000000000)
    | 3 => orderedInterval (56251430773 / 1000000000000) (56251488514 / 1000000000000)
    | _ => orderedInterval (-179306999244 / 1000000000000) (-179306910033 / 1000000000000)

theorem compactCertificate446_stateChecks0 :
    compactCertificate446.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (635 / 2)) (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (187095250383427 / 800000000000)) (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (60502759859491 / 160000000000)) (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks1 :
    compactCertificate446.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (54593927439689 / 800000000000)) (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (146646968374133 / 800000000000)) (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (398175046033761 / 800000000000)) (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks2 :
    compactCertificate446.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (293293936748393 / 800000000000)) (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (502564159653389 / 800000000000)) (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (370186485370151 / 800000000000)) (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks3 :
    compactCertificate446.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (567961266284873 / 800000000000)) (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (327912589978817 / 800000000000)) (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (581886645233653 / 800000000000)) (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks4 :
    compactCertificate446.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (543673984327657 / 800000000000)) (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (387991408839481 / 800000000000)) (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (439940905122399 / 800000000000)) (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks5 :
    compactCertificate446.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (366776860546031 / 800000000000)) (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (324058479518651 / 800000000000)) (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (93924778150449 / 160000000000)) (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks6 :
    compactCertificate446.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (259800879354403 / 800000000000)) (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (220236082644683 / 800000000000)) (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (137813514629849 / 800000000000)) (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks7 :
    compactCertificate446.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (74116566514983 / 800000000000)) (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201240895813949 / 800000000000)) (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (274777238620573 / 800000000000)) (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_stateChecks8 :
    compactCertificate446.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116186485370151 / 800000000000)) (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (472291612548871 / 800000000000)) (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (315468909270089 / 800000000000)) (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_states : ∀ j,
    BesselStateValid (compactCertificate446.point j) (compactCertificate446.state j) :=
  compactCertificate446.statesValid_of_checks3 compactCertificate446_stateChecks0
    compactCertificate446_stateChecks1 compactCertificate446_stateChecks2
    compactCertificate446_stateChecks3 compactCertificate446_stateChecks4
    compactCertificate446_stateChecks5 compactCertificate446_stateChecks6
    compactCertificate446_stateChecks7 compactCertificate446_stateChecks8

theorem compactCertificate446_chunkChecks0_0 :
    compactCertificate446.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (635 / 2) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (187095250383427 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (60502759859491 / 160000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000)))) (orderedInterval (-12132423673 / 1000000000000) (-12132422155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (54593927439689 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (146646968374133 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (398175046033761 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000)))) (orderedInterval (-9898317 / 1000000000000) (-9891848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (293293936748393 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (502564159653389 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (370186485370151 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000)))) (orderedInterval (-1499646728 / 1000000000000) (-1499646660 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks0_1 :
    compactCertificate446.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (567961266284873 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (327912589978817 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (581886645233653 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000)))) (orderedInterval (-4066862502 / 1000000000000) (-4066859212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (543673984327657 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (387991408839481 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (439940905122399 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000)))) (orderedInterval (2757234109 / 1000000000000) (2757237596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (366776860546031 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (324058479518651 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (93924778150449 / 160000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000)))) (orderedInterval (1225515707 / 1000000000000) (1225515738 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks0_2 :
    compactCertificate446.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (259800879354403 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (220236082644683 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (137813514629849 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000)))) (orderedInterval (7064451984 / 1000000000000) (7064454204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (74116566514983 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (201240895813949 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (274777238620573 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000)))) (orderedInterval (3346514721 / 1000000000000) (3346516890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (116186485370151 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (472291612548871 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (315468909270089 / 800000000000) 0 (IntervalRat.scale (635 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000)))) (orderedInterval (4014121336 / 1000000000000) (4014123321 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks0 :
    compactCertificate446.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate446.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate446_chunkChecks0_0
    compactCertificate446_chunkChecks0_1 compactCertificate446_chunkChecks0_2

theorem compactCertificate446_chunkChecks1_0 :
    compactCertificate446.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (635 / 2) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (187095250383427 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (60502759859491 / 160000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000)))) (orderedInterval (-11034483530 / 1000000000000) (-11034482010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (54593927439689 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (146646968374133 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (398175046033761 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000)))) (orderedInterval (1518625472 / 1000000000000) (1518635487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (293293936748393 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (502564159653389 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (370186485370151 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000)))) (orderedInterval (-1344492697 / 1000000000000) (-1344492593 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks1_1 :
    compactCertificate446.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (567961266284873 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (327912589978817 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (581886645233653 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000)))) (orderedInterval (-3895727862 / 1000000000000) (-3895723312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (543673984327657 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (387991408839481 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (439940905122399 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000)))) (orderedInterval (-1595202435 / 1000000000000) (-1595196925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (366776860546031 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (324058479518651 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (93924778150449 / 160000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000)))) (orderedInterval (1446090368 / 1000000000000) (1446090412 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks1_2 :
    compactCertificate446.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (259800879354403 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (220236082644683 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (137813514629849 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000)))) (orderedInterval (-5933677936 / 1000000000000) (-5933675676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (74116566514983 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (201240895813949 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (274777238620573 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000)))) (orderedInterval (-1683259274 / 1000000000000) (-1683258382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (116186485370151 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (472291612548871 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (315468909270089 / 800000000000) 1 (IntervalRat.scale (635 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000)))) (orderedInterval (-11324638726 / 1000000000000) (-11324636245 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks1 :
    compactCertificate446.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate446.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate446_chunkChecks1_0
    compactCertificate446_chunkChecks1_1 compactCertificate446_chunkChecks1_2

theorem compactCertificate446_chunkChecks2_0 :
    compactCertificate446.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (635 / 2) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (187095250383427 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (60502759859491 / 160000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000)))) (orderedInterval (11408981039 / 1000000000000) (11408982642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (54593927439689 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (146646968374133 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (398175046033761 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000)))) (orderedInterval (4596444029 / 1000000000000) (4596459689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (293293936748393 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (502564159653389 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (370186485370151 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000)))) (orderedInterval (4284088238 / 1000000000000) (4284088399 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks2_1 :
    compactCertificate446.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (567961266284873 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (327912589978817 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (581886645233653 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000)))) (orderedInterval (28480678829 / 1000000000000) (28480685405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (543673984327657 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (387991408839481 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (439940905122399 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000)))) (orderedInterval (-5309228643 / 1000000000000) (-5309219817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (366776860546031 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (324058479518651 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (93924778150449 / 160000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000)))) (orderedInterval (-1608239826 / 1000000000000) (-1608239759 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks2_2 :
    compactCertificate446.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (259800879354403 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (220236082644683 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (137813514629849 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000)))) (orderedInterval (-7463056692 / 1000000000000) (-7463054383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (74116566514983 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (201240895813949 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (274777238620573 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000)))) (orderedInterval (-3222856087 / 1000000000000) (-3222855545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (116186485370151 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (472291612548871 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (315468909270089 / 800000000000) 2 (IntervalRat.scale (635 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000)))) (orderedInterval (-3036560271 / 1000000000000) (-3036557155 / 1000000000000))) = true
  rfl'

theorem compactCertificate446_chunkChecks2 :
    compactCertificate446.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate446.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate446_chunkChecks2_0
    compactCertificate446_chunkChecks2_1 compactCertificate446_chunkChecks2_2

theorem compactCertificate446_chunkChecks3_0 :
    compactCertificate446.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (635 / 2) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (187095250383427 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (60502759859491 / 160000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000)))) (orderedInterval (11335233632 / 1000000000000) (11335235384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (54593927439689 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (146646968374133 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (398175046033761 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000)))) (orderedInterval (-5100151798 / 1000000000000) (-5100127292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (293293936748393 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (502564159653389 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (370186485370151 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000)))) (orderedInterval (5563479208 / 1000000000000) (5563479462 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate446_chunkChecks3_1 :
    compactCertificate446.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (567961266284873 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (327912589978817 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (581886645233653 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000)))) (orderedInterval (9480832696 / 1000000000000) (9480842757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (543673984327657 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (387991408839481 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (439940905122399 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000)))) (orderedInterval (3030882842 / 1000000000000) (3030897167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (366776860546031 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (324058479518651 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (93924778150449 / 160000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000)))) (orderedInterval (47939523 / 1000000000000) (47939625 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate446_chunkChecks3_2 :
    compactCertificate446.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (259800879354403 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (220236082644683 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (137813514629849 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000)))) (orderedInterval (4806900669 / 1000000000000) (4806903024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (74116566514983 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (201240895813949 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (274777238620573 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000)))) (orderedInterval (1386079076 / 1000000000000) (1386079536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (116186485370151 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (472291612548871 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (315468909270089 / 800000000000) 3 (IntervalRat.scale (635 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000)))) (orderedInterval (25700234925 / 1000000000000) (25700238851 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate446_chunkChecks3 :
    compactCertificate446.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate446.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate446_chunkChecks3_0
    compactCertificate446_chunkChecks3_1 compactCertificate446_chunkChecks3_2

theorem compactCertificate446_chunkChecks4_0 :
    compactCertificate446.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (635 / 2) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37291391367 / 1000000000000) (-37291391366 / 1000000000000), orderedInterval (-24729432265 / 1000000000000) (-24729432264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (187095250383427 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42904963425 / 1000000000000) (42905031026 / 1000000000000), orderedInterval (-29778111568 / 1000000000000) (-29778043967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (60502759859491 / 160000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38322149038 / 1000000000000) (38322163782 / 1000000000000), orderedInterval (-14712089069 / 1000000000000) (-14712074325 / 1000000000000)))) (orderedInterval (-10209852114 / 1000000000000) (-10209850138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (54593927439689 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-8590674002 / 1000000000000) (-8590673969 / 1000000000000), orderedInterval (96267130356 / 1000000000000) (96267130389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (146646968374133 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56117857924 / 1000000000000) (56117860964 / 1000000000000), orderedInterval (-18145102764 / 1000000000000) (-18145099724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (398175046033761 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30272422878 / 1000000000000) (30272511776 / 1000000000000), orderedInterval (-19073893047 / 1000000000000) (-19073804149 / 1000000000000)))) (orderedInterval (-12736156941 / 1000000000000) (-12736118472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (293293936748393 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6797780692 / 1000000000000) (6797780702 / 1000000000000), orderedInterval (-41122050802 / 1000000000000) (-41122050792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (502564159653389 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19814954426 / 1000000000000) (19814954427 / 1000000000000), orderedInterval (24899330328 / 1000000000000) (24899330329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (370186485370151 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36762382164 / 1000000000000) (-36762380116 / 1000000000000), orderedInterval (4970069398 / 1000000000000) (4970071445 / 1000000000000)))) (orderedInterval (-13410478801 / 1000000000000) (-13410478390 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate446_chunkChecks4_1 :
    compactCertificate446.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (567961266284873 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20122193448 / 1000000000000) (20122193449 / 1000000000000), orderedInterval (22162529509 / 1000000000000) (22162529510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (327912589978817 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30193354883 / 1000000000000) (30193394847 / 1000000000000), orderedInterval (-25364798122 / 1000000000000) (-25364758157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (581886645233653 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19193511545 / 1000000000000) (-19193510115 / 1000000000000), orderedInterval (22526708512 / 1000000000000) (22526709942 / 1000000000000)))) (orderedInterval (-158383661671 / 1000000000000) (-158383645067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (543673984327657 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29849543112 / 1000000000000) (29849559385 / 1000000000000), orderedInterval (-6787395788 / 1000000000000) (-6787379515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (387991408839481 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33393873049 / 1000000000000) (33393906408 / 1000000000000), orderedInterval (-14087726670 / 1000000000000) (-14087693311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (439940905122399 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27327017383 / 1000000000000) (-27327017382 / 1000000000000), orderedInterval (-20245328010 / 1000000000000) (-20245328009 / 1000000000000)))) (orderedInterval (7106845507 / 1000000000000) (7106869236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (366776860546031 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20535676810 / 1000000000000) (20535676811 / 1000000000000), orderedInterval (31071937941 / 1000000000000) (31071937942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (324058479518651 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22146226446 / 1000000000000) (-22146226445 / 1000000000000), orderedInterval (-32853693622 / 1000000000000) (-32853693621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (93924778150449 / 160000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10895914250 / 1000000000000) (-10895914249 / 1000000000000), orderedInterval (-31067323458 / 1000000000000) (-31067323457 / 1000000000000)))) (orderedInterval (1128398194 / 1000000000000) (1128398354 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate446_chunkChecks4_2 :
    compactCertificate446.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (259800879354403 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41096257384 / 1000000000000) (-41096244156 / 1000000000000), orderedInterval (16538334352 / 1000000000000) (16538347581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (220236082644683 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17841715751 / 1000000000000) (-17841715308 / 1000000000000), orderedInterval (44688595336 / 1000000000000) (44688595779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (137813514629849 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15861244479 / 1000000000000) (-15861244478 / 1000000000000), orderedInterval (-58639376755 / 1000000000000) (-58639376753 / 1000000000000)))) (orderedInterval (7687812863 / 1000000000000) (7687815274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (74116566514983 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60495855928 / 1000000000000) (-60495756690 / 1000000000000), orderedInterval (56999192624 / 1000000000000) (56999291862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (201240895813949 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42564115527 / 1000000000000) (42564115528 / 1000000000000), orderedInterval (26730893436 / 1000000000000) (26730893437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (274777238620573 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41690333224 / 1000000000000) (-41690329331 / 1000000000000), orderedInterval (10803161448 / 1000000000000) (10803165341 / 1000000000000)))) (orderedInterval (3994793256 / 1000000000000) (3994793718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (116186485370151 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66061351368 / 1000000000000) (66061351385 / 1000000000000), orderedInterval (4166469191 / 1000000000000) (4166469208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (472291612548871 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16608849156 / 1000000000000) (16608849157 / 1000000000000), orderedInterval (28314305261 / 1000000000000) (28314305262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (315468909270089 / 800000000000) 4 (IntervalRat.scale (635 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26477458692 / 1000000000000) (-26477448581 / 1000000000000), orderedInterval (30255306176 / 1000000000000) (30255316287 / 1000000000000)))) (orderedInterval (-4484699537 / 1000000000000) (-4484694548 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate446_chunkChecks4 :
    compactCertificate446.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate446.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate446_chunkChecks4_0
    compactCertificate446_chunkChecks4_1 compactCertificate446_chunkChecks4_2

theorem compactCertificate446_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate446.chunkCheck r b = true :=
  compactCertificate446.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate446_chunkChecks0
    · exact compactCertificate446_chunkChecks1
    · exact compactCertificate446_chunkChecks2
    · exact compactCertificate446_chunkChecks3
    · exact compactCertificate446_chunkChecks4)

theorem compactCertificate446_coefficient0 :
    compactCertificate446.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate446_coefficient1 :
    compactCertificate446.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate446_coefficient2 :
    compactCertificate446.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate446_coefficient3 :
    compactCertificate446.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate446_coefficient4 :
    compactCertificate446.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate446_coefficients : ∀ r : Fin 5,
    compactCertificate446.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate446_coefficient0
  · exact compactCertificate446_coefficient1
  · exact compactCertificate446_coefficient2
  · exact compactCertificate446_coefficient3
  · exact compactCertificate446_coefficient4

theorem compactCertificate446_lower : (1 : ℚ) ≤ compactCertificate446.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate446, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate446_proves {t : ℝ} (ht : t ∈ compactCertificate446.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate446.proves compactCertificate446_states compactCertificate446_chunks
    compactCertificate446_coefficients compactCertificate446_lower ht

end Erdos232
