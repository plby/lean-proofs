/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate297 : CompactCertificate where
  left := 170
  right := 171
  center := 341 / 2
  grid := fun i =>
    match i.val with
    | 0 => 54
    | 1 => 40
    | 2 => 65
    | 3 => 12
    | 4 => 31
    | 5 => 85
    | 6 => 63
    | 7 => 107
    | 8 => 79
    | 9 => 121
    | 10 => 70
    | 11 => 124
    | 12 => 116
    | 13 => 83
    | 14 => 94
    | 15 => 78
    | 16 => 69
    | 17 => 100
    | 18 => 56
    | 19 => 47
    | 20 => 29
    | 21 => 16
    | 22 => 43
    | 23 => 59
    | 24 => 25
    | 25 => 101
    | _ => 67
  point := fun i =>
    match i.val with
    | 0 => 341 / 2
    | 1 => 502358113234241 / 4000000000000
    | 2 => 162452292221153 / 800000000000
    | 3 => 146586844542787 / 4000000000000
    | 4 => 393752883587239 / 4000000000000
    | 5 => 1069115674783563 / 4000000000000
    | 6 => 787505767174819 / 4000000000000
    | 7 => 1349404554659887 / 4000000000000
    | 8 => 993965287489933 / 4000000000000
    | 9 => 1524998360654659 / 4000000000000
    | 10 => 880458214037611 / 4000000000000
    | 11 => 1562388551375399 / 4000000000000
    | 12 => 1459786052407331 / 4000000000000
    | 13 => 1041772207986323 / 4000000000000
    | 14 => 1181258650761717 / 4000000000000
    | 15 => 984810310599973 / 4000000000000
    | 16 => 870109775715433 / 4000000000000
    | 17 => 252191727159867 / 800000000000
    | 18 => 697575589447649 / 4000000000000
    | 19 => 591342552612889 / 4000000000000
    | 20 => 370034712510067 / 4000000000000
    | 21 => 199005899067789 / 4000000000000
    | 22 => 540339728130367 / 4000000000000
    | 23 => 737787703697759 / 4000000000000
    | 24 => 311965287489933 / 4000000000000
    | 25 => 1268121573851693 / 4000000000000
    | _ => 847046441425987 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))
    | 1 => (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))
    | 2 => (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000))
    | 3 => (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))
    | 4 => (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))
    | 5 => (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000))
    | 6 => (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))
    | 7 => (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))
    | 8 => (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000))
    | 9 => (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))
    | 10 => (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))
    | 11 => (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000))
    | 12 => (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))
    | 13 => (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))
    | 14 => (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000))
    | 15 => (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))
    | 16 => (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))
    | 17 => (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000))
    | 18 => (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))
    | 19 => (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))
    | 20 => (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000))
    | 21 => (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))
    | 22 => (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))
    | 23 => (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000))
    | 24 => (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))
    | 25 => (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))
    | _ => (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (25733739035 / 1000000000000) (25733739135 / 1000000000000)
      | 1 => orderedInterval (517735609 / 1000000000000) (517735675 / 1000000000000)
      | 2 => orderedInterval (141363449 / 1000000000000) (141364059 / 1000000000000)
      | 3 => orderedInterval (15748086475 / 1000000000000) (15748089171 / 1000000000000)
      | 4 => orderedInterval (-3036193785 / 1000000000000) (-3036193764 / 1000000000000)
      | 5 => orderedInterval (4742586731 / 1000000000000) (4742586980 / 1000000000000)
      | 6 => orderedInterval (7438614140 / 1000000000000) (7438621689 / 1000000000000)
      | 7 => orderedInterval (-7909509 / 1000000000000) (-7909487 / 1000000000000)
      | _ => orderedInterval (10750452761 / 1000000000000) (10750456836 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5018794049 / 1000000000000) (-5018793943 / 1000000000000)
      | 1 => orderedInterval (2948793487 / 1000000000000) (2948793535 / 1000000000000)
      | 2 => orderedInterval (-1893119537 / 1000000000000) (-1893118333 / 1000000000000)
      | 3 => orderedInterval (-5796296411 / 1000000000000) (-5796290353 / 1000000000000)
      | 4 => orderedInterval (-7047050759 / 1000000000000) (-7047050725 / 1000000000000)
      | 5 => orderedInterval (-827912223 / 1000000000000) (-827911811 / 1000000000000)
      | 6 => orderedInterval (-4568451795 / 1000000000000) (-4568444700 / 1000000000000)
      | 7 => orderedInterval (5123256557 / 1000000000000) (5123256578 / 1000000000000)
      | _ => orderedInterval (-370374459 / 1000000000000) (-370369389 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-25982273501 / 1000000000000) (-25982273385 / 1000000000000)
      | 1 => orderedInterval (-6392254236 / 1000000000000) (-6392254190 / 1000000000000)
      | 2 => orderedInterval (-2484961971 / 1000000000000) (-2484959586 / 1000000000000)
      | 3 => orderedInterval (-68996372338 / 1000000000000) (-68996358682 / 1000000000000)
      | 4 => orderedInterval (8873481191 / 1000000000000) (8873481247 / 1000000000000)
      | 5 => orderedInterval (-9936619747 / 1000000000000) (-9936619048 / 1000000000000)
      | 6 => orderedInterval (-8513919858 / 1000000000000) (-8513912899 / 1000000000000)
      | 7 => orderedInterval (-28064345 / 1000000000000) (-28064324 / 1000000000000)
      | _ => orderedInterval (-20187987123 / 1000000000000) (-20187980781 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (6877719915 / 1000000000000) (6877720041 / 1000000000000)
      | 1 => orderedInterval (-6974786450 / 1000000000000) (-6974786393 / 1000000000000)
      | 2 => orderedInterval (5956062669 / 1000000000000) (5956067383 / 1000000000000)
      | 3 => orderedInterval (39615685306 / 1000000000000) (39615716038 / 1000000000000)
      | 4 => orderedInterval (17523403288 / 1000000000000) (17523403382 / 1000000000000)
      | 5 => orderedInterval (2659658985 / 1000000000000) (2659660183 / 1000000000000)
      | 6 => orderedInterval (6007351694 / 1000000000000) (6007358625 / 1000000000000)
      | 7 => orderedInterval (-6157460003 / 1000000000000) (-6157459981 / 1000000000000)
      | _ => orderedInterval (-10928883945 / 1000000000000) (-10928876040 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (26497741498 / 1000000000000) (26497741637 / 1000000000000)
      | 1 => orderedInterval (17712933714 / 1000000000000) (17712933794 / 1000000000000)
      | 2 => orderedInterval (13828132968 / 1000000000000) (13828142315 / 1000000000000)
      | 3 => orderedInterval (333439028357 / 1000000000000) (333439097719 / 1000000000000)
      | 4 => orderedInterval (-28644743415 / 1000000000000) (-28644743251 / 1000000000000)
      | 5 => orderedInterval (23412244664 / 1000000000000) (23412246750 / 1000000000000)
      | 6 => orderedInterval (8676538515 / 1000000000000) (8676545542 / 1000000000000)
      | 7 => orderedInterval (-252219993 / 1000000000000) (-252219970 / 1000000000000)
      | _ => orderedInterval (43192602616 / 1000000000000) (43192612535 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (62028474906 / 1000000000000) (62028490294 / 1000000000000)
    | 1 => orderedInterval (-17449949189 / 1000000000000) (-17449929141 / 1000000000000)
    | 2 => orderedInterval (-133648971928 / 1000000000000) (-133648941648 / 1000000000000)
    | 3 => orderedInterval (54578751459 / 1000000000000) (54578803238 / 1000000000000)
    | _ => orderedInterval (437862258924 / 1000000000000) (437862357071 / 1000000000000)

theorem compactCertificate297_stateChecks0 :
    compactCertificate297.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (341 / 2)) (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (502358113234241 / 4000000000000)) (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (162452292221153 / 800000000000)) (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks1 :
    compactCertificate297.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (146586844542787 / 4000000000000)) (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (393752883587239 / 4000000000000)) (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1069115674783563 / 4000000000000)) (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks2 :
    compactCertificate297.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (787505767174819 / 4000000000000)) (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1349404554659887 / 4000000000000)) (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (993965287489933 / 4000000000000)) (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks3 :
    compactCertificate297.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1524998360654659 / 4000000000000)) (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (880458214037611 / 4000000000000)) (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1562388551375399 / 4000000000000)) (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks4 :
    compactCertificate297.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1459786052407331 / 4000000000000)) (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1041772207986323 / 4000000000000)) (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1181258650761717 / 4000000000000)) (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks5 :
    compactCertificate297.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (984810310599973 / 4000000000000)) (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (870109775715433 / 4000000000000)) (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (252191727159867 / 800000000000)) (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks6 :
    compactCertificate297.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (697575589447649 / 4000000000000)) (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (591342552612889 / 4000000000000)) (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (370034712510067 / 4000000000000)) (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks7 :
    compactCertificate297.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (199005899067789 / 4000000000000)) (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (540339728130367 / 4000000000000)) (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (737787703697759 / 4000000000000)) (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_stateChecks8 :
    compactCertificate297.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (311965287489933 / 4000000000000)) (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1268121573851693 / 4000000000000)) (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (847046441425987 / 4000000000000)) (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_states : ∀ j,
    BesselStateValid (compactCertificate297.point j) (compactCertificate297.state j) :=
  compactCertificate297.statesValid_of_checks3 compactCertificate297_stateChecks0
    compactCertificate297_stateChecks1 compactCertificate297_stateChecks2
    compactCertificate297_stateChecks3 compactCertificate297_stateChecks4
    compactCertificate297_stateChecks5 compactCertificate297_stateChecks6
    compactCertificate297_stateChecks7 compactCertificate297_stateChecks8

theorem compactCertificate297_chunkChecks0_0 :
    compactCertificate297.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (341 / 2) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (502358113234241 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (162452292221153 / 800000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000)))) (orderedInterval (25733739035 / 1000000000000) (25733739135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (146586844542787 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (393752883587239 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1069115674783563 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000)))) (orderedInterval (517735609 / 1000000000000) (517735675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (787505767174819 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1349404554659887 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (993965287489933 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000)))) (orderedInterval (141363449 / 1000000000000) (141364059 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks0_1 :
    compactCertificate297.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1524998360654659 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (880458214037611 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1562388551375399 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000)))) (orderedInterval (15748086475 / 1000000000000) (15748089171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1459786052407331 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1041772207986323 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1181258650761717 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000)))) (orderedInterval (-3036193785 / 1000000000000) (-3036193764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (984810310599973 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (870109775715433 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (252191727159867 / 800000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000)))) (orderedInterval (4742586731 / 1000000000000) (4742586980 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks0_2 :
    compactCertificate297.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (697575589447649 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (591342552612889 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (370034712510067 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000)))) (orderedInterval (7438614140 / 1000000000000) (7438621689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (199005899067789 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (540339728130367 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (737787703697759 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000)))) (orderedInterval (-7909509 / 1000000000000) (-7909487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (311965287489933 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1268121573851693 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (847046441425987 / 4000000000000) 0 (IntervalRat.scale (341 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000)))) (orderedInterval (10750452761 / 1000000000000) (10750456836 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks0 :
    compactCertificate297.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate297.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate297_chunkChecks0_0
    compactCertificate297_chunkChecks0_1 compactCertificate297_chunkChecks0_2

theorem compactCertificate297_chunkChecks1_0 :
    compactCertificate297.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (341 / 2) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (502358113234241 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (162452292221153 / 800000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000)))) (orderedInterval (-5018794049 / 1000000000000) (-5018793943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (146586844542787 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (393752883587239 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1069115674783563 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000)))) (orderedInterval (2948793487 / 1000000000000) (2948793535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (787505767174819 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1349404554659887 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (993965287489933 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000)))) (orderedInterval (-1893119537 / 1000000000000) (-1893118333 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks1_1 :
    compactCertificate297.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1524998360654659 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (880458214037611 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1562388551375399 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000)))) (orderedInterval (-5796296411 / 1000000000000) (-5796290353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1459786052407331 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1041772207986323 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1181258650761717 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000)))) (orderedInterval (-7047050759 / 1000000000000) (-7047050725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (984810310599973 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (870109775715433 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (252191727159867 / 800000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000)))) (orderedInterval (-827912223 / 1000000000000) (-827911811 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks1_2 :
    compactCertificate297.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (697575589447649 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (591342552612889 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (370034712510067 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000)))) (orderedInterval (-4568451795 / 1000000000000) (-4568444700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (199005899067789 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (540339728130367 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (737787703697759 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000)))) (orderedInterval (5123256557 / 1000000000000) (5123256578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (311965287489933 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1268121573851693 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (847046441425987 / 4000000000000) 1 (IntervalRat.scale (341 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000)))) (orderedInterval (-370374459 / 1000000000000) (-370369389 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks1 :
    compactCertificate297.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate297.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate297_chunkChecks1_0
    compactCertificate297_chunkChecks1_1 compactCertificate297_chunkChecks1_2

theorem compactCertificate297_chunkChecks2_0 :
    compactCertificate297.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (341 / 2) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (502358113234241 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (162452292221153 / 800000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000)))) (orderedInterval (-25982273501 / 1000000000000) (-25982273385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (146586844542787 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (393752883587239 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1069115674783563 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000)))) (orderedInterval (-6392254236 / 1000000000000) (-6392254190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (787505767174819 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1349404554659887 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (993965287489933 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000)))) (orderedInterval (-2484961971 / 1000000000000) (-2484959586 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks2_1 :
    compactCertificate297.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1524998360654659 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (880458214037611 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1562388551375399 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000)))) (orderedInterval (-68996372338 / 1000000000000) (-68996358682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1459786052407331 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1041772207986323 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1181258650761717 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000)))) (orderedInterval (8873481191 / 1000000000000) (8873481247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (984810310599973 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (870109775715433 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (252191727159867 / 800000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000)))) (orderedInterval (-9936619747 / 1000000000000) (-9936619048 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks2_2 :
    compactCertificate297.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (697575589447649 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (591342552612889 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (370034712510067 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000)))) (orderedInterval (-8513919858 / 1000000000000) (-8513912899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (199005899067789 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (540339728130367 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (737787703697759 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000)))) (orderedInterval (-28064345 / 1000000000000) (-28064324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (311965287489933 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1268121573851693 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (847046441425987 / 4000000000000) 2 (IntervalRat.scale (341 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000)))) (orderedInterval (-20187987123 / 1000000000000) (-20187980781 / 1000000000000))) = true
  rfl'

theorem compactCertificate297_chunkChecks2 :
    compactCertificate297.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate297.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate297_chunkChecks2_0
    compactCertificate297_chunkChecks2_1 compactCertificate297_chunkChecks2_2

theorem compactCertificate297_chunkChecks3_0 :
    compactCertificate297.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (341 / 2) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (502358113234241 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (162452292221153 / 800000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000)))) (orderedInterval (6877719915 / 1000000000000) (6877720041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (146586844542787 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (393752883587239 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1069115674783563 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000)))) (orderedInterval (-6974786450 / 1000000000000) (-6974786393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (787505767174819 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1349404554659887 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (993965287489933 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000)))) (orderedInterval (5956062669 / 1000000000000) (5956067383 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate297_chunkChecks3_1 :
    compactCertificate297.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1524998360654659 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (880458214037611 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1562388551375399 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000)))) (orderedInterval (39615685306 / 1000000000000) (39615716038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1459786052407331 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1041772207986323 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1181258650761717 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000)))) (orderedInterval (17523403288 / 1000000000000) (17523403382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (984810310599973 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (870109775715433 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (252191727159867 / 800000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000)))) (orderedInterval (2659658985 / 1000000000000) (2659660183 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate297_chunkChecks3_2 :
    compactCertificate297.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (697575589447649 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (591342552612889 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (370034712510067 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000)))) (orderedInterval (6007351694 / 1000000000000) (6007358625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (199005899067789 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (540339728130367 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (737787703697759 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000)))) (orderedInterval (-6157460003 / 1000000000000) (-6157459981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (311965287489933 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1268121573851693 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (847046441425987 / 4000000000000) 3 (IntervalRat.scale (341 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000)))) (orderedInterval (-10928883945 / 1000000000000) (-10928876040 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate297_chunkChecks3 :
    compactCertificate297.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate297.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate297_chunkChecks3_0
    compactCertificate297_chunkChecks3_1 compactCertificate297_chunkChecks3_2

theorem compactCertificate297_chunkChecks4_0 :
    compactCertificate297.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (341 / 2) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (60964364169 / 1000000000000) (60964364314 / 1000000000000), orderedInterval (-4322533117 / 1000000000000) (-4322532973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (502358113234241 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46420751959 / 1000000000000) (46420751960 / 1000000000000), orderedInterval (53798255440 / 1000000000000) (53798255441 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (162452292221153 / 800000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19376718187 / 1000000000000) (19376718688 / 1000000000000), orderedInterval (-52579591547 / 1000000000000) (-52579591046 / 1000000000000)))) (orderedInterval (26497741498 / 1000000000000) (26497741637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (146586844542787 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-35206499725 / 1000000000000) (-35206499232 / 1000000000000), orderedInterval (127498758608 / 1000000000000) (127498759101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (393752883587239 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77670259493 / 1000000000000) (-77670258407 / 1000000000000), orderedInterval (21238200900 / 1000000000000) (21238201987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1069115674783563 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-41801404662 / 1000000000000) (-41801404661 / 1000000000000), orderedInterval (-25111009350 / 1000000000000) (-25111009349 / 1000000000000)))) (orderedInterval (17712933714 / 1000000000000) (17712933794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (787505767174819 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14571101261 / 1000000000000) (14571101413 / 1000000000000), orderedInterval (-55003291782 / 1000000000000) (-55003291630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1349404554659887 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39754248515 / 1000000000000) (-39754229069 / 1000000000000), orderedInterval (17572112655 / 1000000000000) (17572132101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (993965287489933 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44886412412 / 1000000000000) (-44886412411 / 1000000000000), orderedInterval (-23300848964 / 1000000000000) (-23300848963 / 1000000000000)))) (orderedInterval (13828132968 / 1000000000000) (13828142315 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate297_chunkChecks4_1 :
    compactCertificate297.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1524998360654659 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38643278893 / 1000000000000) (-38643268189 / 1000000000000), orderedInterval (13336772685 / 1000000000000) (13336783389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (880458214037611 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44898765347 / 1000000000000) (44898765348 / 1000000000000), orderedInterval (29500683087 / 1000000000000) (29500683088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1562388551375399 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (39076926127 / 1000000000000) (39076931235 / 1000000000000), orderedInterval (-10191786743 / 1000000000000) (-10191781635 / 1000000000000)))) (orderedInterval (333439028357 / 1000000000000) (333439097719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1459786052407331 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40319459807 / 1000000000000) (40319459812 / 1000000000000), orderedInterval (10842426252 / 1000000000000) (10842426257 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1041772207986323 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22645349225 / 1000000000000) (-22645349224 / 1000000000000), orderedInterval (-43906076527 / 1000000000000) (-43906076526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1181258650761717 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32979244797 / 1000000000000) (32979244798 / 1000000000000), orderedInterval (32626009199 / 1000000000000) (32626009200 / 1000000000000)))) (orderedInterval (-28644743415 / 1000000000000) (-28644743251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (984810310599973 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47364001576 / 1000000000000) (47364009740 / 1000000000000), orderedInterval (-18600326031 / 1000000000000) (-18600317867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (870109775715433 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54076306733 / 1000000000000) (-54076306682 / 1000000000000), orderedInterval (-1413076021 / 1000000000000) (-1413075970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (252191727159867 / 800000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43002565770 / 1000000000000) (43002571015 / 1000000000000), orderedInterval (-13116414483 / 1000000000000) (-13116409238 / 1000000000000)))) (orderedInterval (23412244664 / 1000000000000) (23412246750 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate297_chunkChecks4_2 :
    compactCertificate297.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (697575589447649 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41210901915 / 1000000000000) (-41210863069 / 1000000000000), orderedInterval (44301100820 / 1000000000000) (44301139666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (591342552612889 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53957022701 / 1000000000000) (-53957022700 / 1000000000000), orderedInterval (-37165849699 / 1000000000000) (-37165849698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (370034712510067 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67720415601 / 1000000000000) (-67720375845 / 1000000000000), orderedInterval (48278876642 / 1000000000000) (48278916397 / 1000000000000)))) (orderedInterval (8676538515 / 1000000000000) (8676545542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (199005899067789 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30049456214 / 1000000000000) (30049456215 / 1000000000000), orderedInterval (108755739054 / 1000000000000) (108755739055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (540339728130367 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48324446034 / 1000000000000) (-48324446033 / 1000000000000), orderedInterval (-48580599412 / 1000000000000) (-48580599411 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (737787703697759 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7168331302 / 1000000000000) (7168331325 / 1000000000000), orderedInterval (-58330098749 / 1000000000000) (-58330098726 / 1000000000000)))) (orderedInterval (-252219993 / 1000000000000) (-252219970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (311965287489933 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21063057317 / 1000000000000) (-21063057316 / 1000000000000), orderedInterval (-87723932954 / 1000000000000) (-87723932953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1268121573851693 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22053250286 / 1000000000000) (-22053250285 / 1000000000000), orderedInterval (-38974540756 / 1000000000000) (-38974540755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (847046441425987 / 4000000000000) 4 (IntervalRat.scale (341 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48406044785 / 1000000000000) (-48406023317 / 1000000000000), orderedInterval (25866080419 / 1000000000000) (25866101886 / 1000000000000)))) (orderedInterval (43192602616 / 1000000000000) (43192612535 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate297_chunkChecks4 :
    compactCertificate297.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate297.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate297_chunkChecks4_0
    compactCertificate297_chunkChecks4_1 compactCertificate297_chunkChecks4_2

theorem compactCertificate297_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate297.chunkCheck r b = true :=
  compactCertificate297.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate297_chunkChecks0
    · exact compactCertificate297_chunkChecks1
    · exact compactCertificate297_chunkChecks2
    · exact compactCertificate297_chunkChecks3
    · exact compactCertificate297_chunkChecks4)

theorem compactCertificate297_coefficient0 :
    compactCertificate297.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate297_coefficient1 :
    compactCertificate297.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate297_coefficient2 :
    compactCertificate297.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate297_coefficient3 :
    compactCertificate297.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate297_coefficient4 :
    compactCertificate297.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate297_coefficients : ∀ r : Fin 5,
    compactCertificate297.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate297_coefficient0
  · exact compactCertificate297_coefficient1
  · exact compactCertificate297_coefficient2
  · exact compactCertificate297_coefficient3
  · exact compactCertificate297_coefficient4

theorem compactCertificate297_lower : (1 : ℚ) ≤ compactCertificate297.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate297, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate297_proves {t : ℝ} (ht : t ∈ compactCertificate297.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate297.proves compactCertificate297_states compactCertificate297_chunks
    compactCertificate297_coefficients compactCertificate297_lower ht

end Erdos232
