/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate471 : CompactCertificate where
  left := 342
  right := 343
  center := 685 / 2
  grid := fun i =>
    match i.val with
    | 0 => 109
    | 1 => 80
    | 2 => 130
    | 3 => 23
    | 4 => 63
    | 5 => 171
    | 6 => 126
    | 7 => 216
    | 8 => 159
    | 9 => 244
    | 10 => 141
    | 11 => 250
    | 12 => 233
    | 13 => 167
    | 14 => 189
    | 15 => 158
    | 16 => 139
    | 17 => 202
    | 18 => 112
    | 19 => 95
    | 20 => 59
    | 21 => 32
    | 22 => 86
    | 23 => 118
    | 24 => 50
    | 25 => 203
    | _ => 135
  point := fun i =>
    match i.val with
    | 0 => 685 / 2
    | 1 => 201827159862437 / 800000000000
    | 2 => 65266756698821 / 160000000000
    | 3 => 58892661883759 / 800000000000
    | 4 => 158193973757923 / 800000000000
    | 5 => 429527411863191 / 800000000000
    | 6 => 316387947515983 / 800000000000
    | 7 => 542136140728459 / 800000000000
    | 8 => 399335027525281 / 800000000000
    | 9 => 612682625834863 / 800000000000
    | 10 => 353732478953527 / 800000000000
    | 11 => 627704491315043 / 800000000000
    | 12 => 586482959471567 / 800000000000
    | 13 => 418541913472511 / 800000000000
    | 14 => 474581921273769 / 800000000000
    | 15 => 395656928305561 / 800000000000
    | 16 => 349574895228781 / 800000000000
    | 17 => 101320429973319 / 160000000000
    | 18 => 280257641508293 / 800000000000
    | 19 => 237577506474973 / 800000000000
    | 20 => 148664972474719 / 800000000000
    | 21 => 79952516634273 / 800000000000
    | 22 => 217086635641819 / 800000000000
    | 23 => 296413241661563 / 800000000000
    | 24 => 125335027525281 / 800000000000
    | 25 => 509479928497601 / 800000000000
    | _ => 340308980866159 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))
    | 1 => (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))
    | 2 => (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000))
    | 3 => (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))
    | 4 => (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))
    | 5 => (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000))
    | 6 => (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))
    | 7 => (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))
    | 8 => (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000))
    | 9 => (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))
    | 10 => (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))
    | 11 => (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000))
    | 12 => (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))
    | 13 => (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))
    | 14 => (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000))
    | 15 => (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))
    | 16 => (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))
    | 17 => (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000))
    | 18 => (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))
    | 19 => (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))
    | 20 => (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000))
    | 21 => (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))
    | 22 => (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))
    | 23 => (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000))
    | 24 => (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))
    | 25 => (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))
    | _ => (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11718551128 / 1000000000000) (-11718551095 / 1000000000000)
      | 1 => orderedInterval (801656394 / 1000000000000) (801656702 / 1000000000000)
      | 2 => orderedInterval (-246910198 / 1000000000000) (-246910178 / 1000000000000)
      | 3 => orderedInterval (-349426638 / 1000000000000) (-349426502 / 1000000000000)
      | 4 => orderedInterval (2627998574 / 1000000000000) (2627999928 / 1000000000000)
      | 5 => orderedInterval (1132661981 / 1000000000000) (1132663121 / 1000000000000)
      | 6 => orderedInterval (1160111868 / 1000000000000) (1160115424 / 1000000000000)
      | 7 => orderedInterval (-3075042438 / 1000000000000) (-3075042132 / 1000000000000)
      | _ => orderedInterval (6281945746 / 1000000000000) (6281956244 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8659683559 / 1000000000000) (-8659683525 / 1000000000000)
      | 1 => orderedInterval (2298975720 / 1000000000000) (2298975824 / 1000000000000)
      | 2 => orderedInterval (-2992402896 / 1000000000000) (-2992402862 / 1000000000000)
      | 3 => orderedInterval (-5762835369 / 1000000000000) (-5762835086 / 1000000000000)
      | 4 => orderedInterval (-3998689071 / 1000000000000) (-3998686398 / 1000000000000)
      | 5 => orderedInterval (2914729362 / 1000000000000) (2914731013 / 1000000000000)
      | 6 => orderedInterval (-3664951612 / 1000000000000) (-3664948097 / 1000000000000)
      | 7 => orderedInterval (-2930678863 / 1000000000000) (-2930678616 / 1000000000000)
      | _ => orderedInterval (704975268 / 1000000000000) (704988322 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11672528261 / 1000000000000) (11672528297 / 1000000000000)
      | 1 => orderedInterval (-2441049498 / 1000000000000) (-2441049420 / 1000000000000)
      | 2 => orderedInterval (316046535 / 1000000000000) (316046595 / 1000000000000)
      | 3 => orderedInterval (1875969044 / 1000000000000) (1875969649 / 1000000000000)
      | 4 => orderedInterval (-7280472030 / 1000000000000) (-7280466646 / 1000000000000)
      | 5 => orderedInterval (-914213160 / 1000000000000) (-914210762 / 1000000000000)
      | 6 => orderedInterval (-3061493971 / 1000000000000) (-3061490469 / 1000000000000)
      | 7 => orderedInterval (2749022806 / 1000000000000) (2749023010 / 1000000000000)
      | _ => orderedInterval (-8973186037 / 1000000000000) (-8973169754 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7493440039 / 1000000000000) (7493440079 / 1000000000000)
      | 1 => orderedInterval (-8011738646 / 1000000000000) (-8011738546 / 1000000000000)
      | 2 => orderedInterval (9677473735 / 1000000000000) (9677473844 / 1000000000000)
      | 3 => orderedInterval (14409530386 / 1000000000000) (14409531711 / 1000000000000)
      | 4 => orderedInterval (9990178481 / 1000000000000) (9990189475 / 1000000000000)
      | 5 => orderedInterval (-7159200227 / 1000000000000) (-7159196741 / 1000000000000)
      | 6 => orderedInterval (4123641691 / 1000000000000) (4123645184 / 1000000000000)
      | 7 => orderedInterval (3147012631 / 1000000000000) (3147012801 / 1000000000000)
      | _ => orderedInterval (-9954197045 / 1000000000000) (-9954176763 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11404936633 / 1000000000000) (-11404936587 / 1000000000000)
      | 1 => orderedInterval (6771032018 / 1000000000000) (6771032169 / 1000000000000)
      | 2 => orderedInterval (140851024 / 1000000000000) (140851225 / 1000000000000)
      | 3 => orderedInterval (-9502863732 / 1000000000000) (-9502860789 / 1000000000000)
      | 4 => orderedInterval (22228316307 / 1000000000000) (22228339063 / 1000000000000)
      | 5 => orderedInterval (-1475657973 / 1000000000000) (-1475652884 / 1000000000000)
      | 6 => orderedInterval (3962957160 / 1000000000000) (3962960665 / 1000000000000)
      | 7 => orderedInterval (-2853902614 / 1000000000000) (-2853902469 / 1000000000000)
      | _ => orderedInterval (12017540787 / 1000000000000) (12017566145 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3385555839 / 1000000000000) (-3385538488 / 1000000000000)
    | 1 => orderedInterval (-22090561020 / 1000000000000) (-22090539425 / 1000000000000)
    | 2 => orderedInterval (-6056848050 / 1000000000000) (-6056819500 / 1000000000000)
    | 3 => orderedInterval (23716141045 / 1000000000000) (23716181044 / 1000000000000)
    | _ => orderedInterval (19883336344 / 1000000000000) (19883396538 / 1000000000000)

theorem compactCertificate471_stateChecks0 :
    compactCertificate471.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (685 / 2)) (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201827159862437 / 800000000000)) (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (65266756698821 / 160000000000)) (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks1 :
    compactCertificate471.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (58892661883759 / 800000000000)) (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (158193973757923 / 800000000000)) (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (429527411863191 / 800000000000)) (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks2 :
    compactCertificate471.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (316387947515983 / 800000000000)) (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (542136140728459 / 800000000000)) (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (399335027525281 / 800000000000)) (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks3 :
    compactCertificate471.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (612682625834863 / 800000000000)) (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (353732478953527 / 800000000000)) (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (627704491315043 / 800000000000)) (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks4 :
    compactCertificate471.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (586482959471567 / 800000000000)) (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (418541913472511 / 800000000000)) (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (474581921273769 / 800000000000)) (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks5 :
    compactCertificate471.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (395656928305561 / 800000000000)) (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (349574895228781 / 800000000000)) (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (101320429973319 / 160000000000)) (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks6 :
    compactCertificate471.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280257641508293 / 800000000000)) (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (237577506474973 / 800000000000)) (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148664972474719 / 800000000000)) (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks7 :
    compactCertificate471.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (79952516634273 / 800000000000)) (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (217086635641819 / 800000000000)) (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (296413241661563 / 800000000000)) (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_stateChecks8 :
    compactCertificate471.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125335027525281 / 800000000000)) (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (509479928497601 / 800000000000)) (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (340308980866159 / 800000000000)) (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_states : ∀ j,
    BesselStateValid (compactCertificate471.point j) (compactCertificate471.state j) :=
  compactCertificate471.statesValid_of_checks3 compactCertificate471_stateChecks0
    compactCertificate471_stateChecks1 compactCertificate471_stateChecks2
    compactCertificate471_stateChecks3 compactCertificate471_stateChecks4
    compactCertificate471_stateChecks5 compactCertificate471_stateChecks6
    compactCertificate471_stateChecks7 compactCertificate471_stateChecks8

theorem compactCertificate471_chunkChecks0_0 :
    compactCertificate471.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (685 / 2) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (201827159862437 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (65266756698821 / 160000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000)))) (orderedInterval (-11718551128 / 1000000000000) (-11718551095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (58892661883759 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (158193973757923 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (429527411863191 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000)))) (orderedInterval (801656394 / 1000000000000) (801656702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (316387947515983 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (542136140728459 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (399335027525281 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000)))) (orderedInterval (-246910198 / 1000000000000) (-246910178 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks0_1 :
    compactCertificate471.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (612682625834863 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (353732478953527 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (627704491315043 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000)))) (orderedInterval (-349426638 / 1000000000000) (-349426502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (586482959471567 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (418541913472511 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (474581921273769 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000)))) (orderedInterval (2627998574 / 1000000000000) (2627999928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (395656928305561 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (349574895228781 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (101320429973319 / 160000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000)))) (orderedInterval (1132661981 / 1000000000000) (1132663121 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks0_2 :
    compactCertificate471.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (280257641508293 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (237577506474973 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (148664972474719 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000)))) (orderedInterval (1160111868 / 1000000000000) (1160115424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (79952516634273 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (217086635641819 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (296413241661563 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000)))) (orderedInterval (-3075042438 / 1000000000000) (-3075042132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (125335027525281 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (509479928497601 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (340308980866159 / 800000000000) 0 (IntervalRat.scale (685 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000)))) (orderedInterval (6281945746 / 1000000000000) (6281956244 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks0 :
    compactCertificate471.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate471.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate471_chunkChecks0_0
    compactCertificate471_chunkChecks0_1 compactCertificate471_chunkChecks0_2

theorem compactCertificate471_chunkChecks1_0 :
    compactCertificate471.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (685 / 2) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (201827159862437 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (65266756698821 / 160000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000)))) (orderedInterval (-8659683559 / 1000000000000) (-8659683525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (58892661883759 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (158193973757923 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (429527411863191 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000)))) (orderedInterval (2298975720 / 1000000000000) (2298975824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (316387947515983 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (542136140728459 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (399335027525281 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000)))) (orderedInterval (-2992402896 / 1000000000000) (-2992402862 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks1_1 :
    compactCertificate471.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (612682625834863 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (353732478953527 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (627704491315043 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000)))) (orderedInterval (-5762835369 / 1000000000000) (-5762835086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (586482959471567 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (418541913472511 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (474581921273769 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000)))) (orderedInterval (-3998689071 / 1000000000000) (-3998686398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (395656928305561 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (349574895228781 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (101320429973319 / 160000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000)))) (orderedInterval (2914729362 / 1000000000000) (2914731013 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks1_2 :
    compactCertificate471.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (280257641508293 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (237577506474973 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (148664972474719 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000)))) (orderedInterval (-3664951612 / 1000000000000) (-3664948097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (79952516634273 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (217086635641819 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (296413241661563 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000)))) (orderedInterval (-2930678863 / 1000000000000) (-2930678616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (125335027525281 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (509479928497601 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (340308980866159 / 800000000000) 1 (IntervalRat.scale (685 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000)))) (orderedInterval (704975268 / 1000000000000) (704988322 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks1 :
    compactCertificate471.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate471.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate471_chunkChecks1_0
    compactCertificate471_chunkChecks1_1 compactCertificate471_chunkChecks1_2

theorem compactCertificate471_chunkChecks2_0 :
    compactCertificate471.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (685 / 2) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (201827159862437 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (65266756698821 / 160000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000)))) (orderedInterval (11672528261 / 1000000000000) (11672528297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (58892661883759 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (158193973757923 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (429527411863191 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000)))) (orderedInterval (-2441049498 / 1000000000000) (-2441049420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (316387947515983 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (542136140728459 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (399335027525281 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000)))) (orderedInterval (316046535 / 1000000000000) (316046595 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks2_1 :
    compactCertificate471.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (612682625834863 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (353732478953527 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (627704491315043 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000)))) (orderedInterval (1875969044 / 1000000000000) (1875969649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (586482959471567 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (418541913472511 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (474581921273769 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000)))) (orderedInterval (-7280472030 / 1000000000000) (-7280466646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (395656928305561 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (349574895228781 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (101320429973319 / 160000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000)))) (orderedInterval (-914213160 / 1000000000000) (-914210762 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks2_2 :
    compactCertificate471.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (280257641508293 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (237577506474973 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (148664972474719 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000)))) (orderedInterval (-3061493971 / 1000000000000) (-3061490469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (79952516634273 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (217086635641819 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (296413241661563 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000)))) (orderedInterval (2749022806 / 1000000000000) (2749023010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (125335027525281 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (509479928497601 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (340308980866159 / 800000000000) 2 (IntervalRat.scale (685 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000)))) (orderedInterval (-8973186037 / 1000000000000) (-8973169754 / 1000000000000))) = true
  rfl'

theorem compactCertificate471_chunkChecks2 :
    compactCertificate471.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate471.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate471_chunkChecks2_0
    compactCertificate471_chunkChecks2_1 compactCertificate471_chunkChecks2_2

theorem compactCertificate471_chunkChecks3_0 :
    compactCertificate471.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (685 / 2) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (201827159862437 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (65266756698821 / 160000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000)))) (orderedInterval (7493440039 / 1000000000000) (7493440079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (58892661883759 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (158193973757923 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (429527411863191 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000)))) (orderedInterval (-8011738646 / 1000000000000) (-8011738546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (316387947515983 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (542136140728459 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (399335027525281 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000)))) (orderedInterval (9677473735 / 1000000000000) (9677473844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate471_chunkChecks3_1 :
    compactCertificate471.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (612682625834863 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (353732478953527 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (627704491315043 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000)))) (orderedInterval (14409530386 / 1000000000000) (14409531711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (586482959471567 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (418541913472511 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (474581921273769 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000)))) (orderedInterval (9990178481 / 1000000000000) (9990189475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (395656928305561 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (349574895228781 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (101320429973319 / 160000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000)))) (orderedInterval (-7159200227 / 1000000000000) (-7159196741 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate471_chunkChecks3_2 :
    compactCertificate471.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (280257641508293 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (237577506474973 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (148664972474719 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000)))) (orderedInterval (4123641691 / 1000000000000) (4123645184 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (79952516634273 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (217086635641819 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (296413241661563 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000)))) (orderedInterval (3147012631 / 1000000000000) (3147012801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (125335027525281 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (509479928497601 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (340308980866159 / 800000000000) 3 (IntervalRat.scale (685 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000)))) (orderedInterval (-9954197045 / 1000000000000) (-9954176763 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate471_chunkChecks3 :
    compactCertificate471.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate471.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate471_chunkChecks3_0
    compactCertificate471_chunkChecks3_1 compactCertificate471_chunkChecks3_2

theorem compactCertificate471_chunkChecks4_0 :
    compactCertificate471.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (685 / 2) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32430817420 / 1000000000000) (-32430817419 / 1000000000000), orderedInterval (-28360149248 / 1000000000000) (-28360149247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (201827159862437 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49504047261 / 1000000000000) (49504048177 / 1000000000000), orderedInterval (-8628655045 / 1000000000000) (-8628654128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (65266756698821 / 160000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11496162504 / 1000000000000) (11496162505 / 1000000000000), orderedInterval (37781390078 / 1000000000000) (37781390079 / 1000000000000)))) (orderedInterval (-11404936633 / 1000000000000) (-11404936587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (58892661883759 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78185193689 / 1000000000000) (-78185169166 / 1000000000000), orderedInterval (50878393377 / 1000000000000) (50878417900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (158193973757923 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32359993420 / 1000000000000) (-32359993419 / 1000000000000), orderedInterval (-46525828974 / 1000000000000) (-46525828973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (429527411863191 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15964669500 / 1000000000000) (-15964669499 / 1000000000000), orderedInterval (-30494830412 / 1000000000000) (-30494830411 / 1000000000000)))) (orderedInterval (6771032018 / 1000000000000) (6771032169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (316387947515983 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16701400366 / 1000000000000) (16701400367 / 1000000000000), orderedInterval (36458789947 / 1000000000000) (36458789948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (542136140728459 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3931453773 / 1000000000000) (-3931453772 / 1000000000000), orderedInterval (30399744832 / 1000000000000) (30399744834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (399335027525281 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15233843949 / 1000000000000) (-15233843948 / 1000000000000), orderedInterval (-32284743096 / 1000000000000) (-32284743095 / 1000000000000)))) (orderedInterval (140851024 / 1000000000000) (140851225 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate471_chunkChecks4_1 :
    compactCertificate471.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (612682625834863 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2588742218 / 1000000000000) (2588742219 / 1000000000000), orderedInterval (28713360187 / 1000000000000) (28713360188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (353732478953527 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (525512830 / 1000000000000) (525512831 / 1000000000000), orderedInterval (-37941358080 / 1000000000000) (-37941358078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (627704491315043 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (503851710 / 1000000000000) (503851711 / 1000000000000), orderedInterval (28479648914 / 1000000000000) (28479648915 / 1000000000000)))) (orderedInterval (-9502863732 / 1000000000000) (-9502860789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (586482959471567 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27906549175 / 1000000000000) (-27906494943 / 1000000000000), orderedInterval (9485558547 / 1000000000000) (9485612779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (418541913472511 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22026960769 / 1000000000000) (22026964305 / 1000000000000), orderedInterval (-27070018148 / 1000000000000) (-27070014613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (474581921273769 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8154743961 / 1000000000000) (-8154743960 / 1000000000000), orderedInterval (-31720823746 / 1000000000000) (-31720823745 / 1000000000000)))) (orderedInterval (22228316307 / 1000000000000) (22228339063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (395656928305561 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30483832555 / 1000000000000) (-30483737749 / 1000000000000), orderedInterval (18950447249 / 1000000000000) (18950542056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (349574895228781 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33525190876 / 1000000000000) (-33525190875 / 1000000000000), orderedInterval (-18208871531 / 1000000000000) (-18208871530 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (101320429973319 / 160000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16944886763 / 1000000000000) (-16944886306 / 1000000000000), orderedInterval (26812410361 / 1000000000000) (26812410818 / 1000000000000)))) (orderedInterval (-1475657973 / 1000000000000) (-1475652884 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate471_chunkChecks4_2 :
    compactCertificate471.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (280257641508293 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29097675547 / 1000000000000) (-29097658398 / 1000000000000), orderedInterval (31195451585 / 1000000000000) (31195468735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (237577506474973 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29630057369 / 1000000000000) (29630070217 / 1000000000000), orderedInterval (-35627466319 / 1000000000000) (-35627453470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (148664972474719 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55761264455 / 1000000000000) (-55761264453 / 1000000000000), orderedInterval (-17639486778 / 1000000000000) (-17639486776 / 1000000000000)))) (orderedInterval (3962957160 / 1000000000000) (3962960665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (79952516634273 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15373077592 / 1000000000000) (15373077593 / 1000000000000), orderedInterval (78241165759 / 1000000000000) (78241165760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (217086635641819 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44697523238 / 1000000000000) (44697534905 / 1000000000000), orderedInterval (-18741859666 / 1000000000000) (-18741847999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (296413241661563 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23188362963 / 1000000000000) (23188362964 / 1000000000000), orderedInterval (34327049728 / 1000000000000) (34327049729 / 1000000000000)))) (orderedInterval (-2853902614 / 1000000000000) (-2853902469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (125335027525281 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23274086935 / 1000000000000) (23274086936 / 1000000000000), orderedInterval (59270542137 / 1000000000000) (59270542138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (509479928497601 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (3414174179 / 1000000000000) (3414174180 / 1000000000000), orderedInterval (-31434866980 / 1000000000000) (-31434866979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (340308980866159 / 800000000000) 4 (IntervalRat.scale (685 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34214630064 / 1000000000000) (-34214574619 / 1000000000000), orderedInterval (18093696549 / 1000000000000) (18093751994 / 1000000000000)))) (orderedInterval (12017540787 / 1000000000000) (12017566145 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate471_chunkChecks4 :
    compactCertificate471.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate471.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate471_chunkChecks4_0
    compactCertificate471_chunkChecks4_1 compactCertificate471_chunkChecks4_2

theorem compactCertificate471_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate471.chunkCheck r b = true :=
  compactCertificate471.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate471_chunkChecks0
    · exact compactCertificate471_chunkChecks1
    · exact compactCertificate471_chunkChecks2
    · exact compactCertificate471_chunkChecks3
    · exact compactCertificate471_chunkChecks4)

theorem compactCertificate471_coefficient0 :
    compactCertificate471.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate471_coefficient1 :
    compactCertificate471.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate471_coefficient2 :
    compactCertificate471.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate471_coefficient3 :
    compactCertificate471.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate471_coefficient4 :
    compactCertificate471.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate471_coefficients : ∀ r : Fin 5,
    compactCertificate471.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate471_coefficient0
  · exact compactCertificate471_coefficient1
  · exact compactCertificate471_coefficient2
  · exact compactCertificate471_coefficient3
  · exact compactCertificate471_coefficient4

theorem compactCertificate471_lower : (1 : ℚ) ≤ compactCertificate471.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate471, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate471_proves {t : ℝ} (ht : t ∈ compactCertificate471.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate471.proves compactCertificate471_states compactCertificate471_chunks
    compactCertificate471_coefficients compactCertificate471_lower ht

end Erdos232
