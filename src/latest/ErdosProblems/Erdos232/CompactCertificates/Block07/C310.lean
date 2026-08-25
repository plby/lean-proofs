/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate310 : CompactCertificate where
  left := 183
  right := 184
  center := 367 / 2
  grid := fun i =>
    match i.val with
    | 0 => 58
    | 1 => 43
    | 2 => 70
    | 3 => 13
    | 4 => 34
    | 5 => 92
    | 6 => 67
    | 7 => 116
    | 8 => 85
    | 9 => 131
    | 10 => 75
    | 11 => 134
    | 12 => 125
    | 13 => 89
    | 14 => 101
    | 15 => 84
    | 16 => 75
    | 17 => 108
    | 18 => 60
    | 19 => 51
    | 20 => 32
    | 21 => 17
    | 22 => 46
    | 23 => 63
    | 24 => 27
    | 25 => 109
    | _ => 73
  point := fun i =>
    match i.val with
    | 0 => 367 / 2
    | 1 => 540661077879667 / 4000000000000
    | 2 => 174838684003411 / 800000000000
    | 3 => 157763554097369 / 4000000000000
    | 4 => 423775097585093 / 4000000000000
    | 5 => 1150631825940081 / 4000000000000
    | 6 => 847550195170553 / 4000000000000
    | 7 => 1452291705455069 / 4000000000000
    | 8 => 1069751497093271 / 4000000000000
    | 9 => 1641273895484633 / 4000000000000
    | 10 => 947589925371857 / 4000000000000
    | 11 => 1681514951187013 / 4000000000000
    | 12 => 1571089387781497 / 4000000000000
    | 13 => 1121203520032201 / 4000000000000
    | 14 => 1271325292755279 / 4000000000000
    | 15 => 1059898486774751 / 4000000000000
    | 16 => 936452456561771 / 4000000000000
    | 17 => 271420421899329 / 800000000000
    | 18 => 750763171047763 / 4000000000000
    | 19 => 636430254571643 / 4000000000000
    | 20 => 398248502906729 / 4000000000000
    | 21 => 214179369377943 / 4000000000000
    | 22 => 581538651682829 / 4000000000000
    | 23 => 794041311604333 / 4000000000000
    | 24 => 335751497093271 / 4000000000000
    | 25 => 1364811195318391 / 4000000000000
    | _ => 911630627575769 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))
    | 1 => (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))
    | 2 => (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000))
    | 3 => (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))
    | 4 => (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
    | 5 => (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000))
    | 6 => (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))
    | 7 => (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))
    | 8 => (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000))
    | 9 => (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))
    | 10 => (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))
    | 11 => (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000))
    | 12 => (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))
    | 13 => (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))
    | 14 => (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000))
    | 15 => (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))
    | 16 => (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))
    | 17 => (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000))
    | 18 => (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))
    | 19 => (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))
    | 20 => (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000))
    | 21 => (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))
    | 22 => (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))
    | 23 => (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000))
    | 24 => (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))
    | 25 => (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))
    | _ => (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18254573771 / 1000000000000) (18254582514 / 1000000000000)
      | 1 => orderedInterval (801144081 / 1000000000000) (801144642 / 1000000000000)
      | 2 => orderedInterval (-400109938 / 1000000000000) (-400109853 / 1000000000000)
      | 3 => orderedInterval (-5351265859 / 1000000000000) (-5351263865 / 1000000000000)
      | 4 => orderedInterval (-3720493872 / 1000000000000) (-3720493846 / 1000000000000)
      | 5 => orderedInterval (-658518671 / 1000000000000) (-658517315 / 1000000000000)
      | 6 => orderedInterval (-1448453630 / 1000000000000) (-1448453552 / 1000000000000)
      | 7 => orderedInterval (4363982792 / 1000000000000) (4363982818 / 1000000000000)
      | _ => orderedInterval (-7414820834 / 1000000000000) (-7414818664 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8422438100 / 1000000000000) (-8422429289 / 1000000000000)
      | 1 => orderedInterval (-2507481998 / 1000000000000) (-2507481438 / 1000000000000)
      | 2 => orderedInterval (-2797621561 / 1000000000000) (-2797621397 / 1000000000000)
      | 3 => orderedInterval (28927276266 / 1000000000000) (28927278968 / 1000000000000)
      | 4 => orderedInterval (530000018 / 1000000000000) (530000059 / 1000000000000)
      | 5 => orderedInterval (4097069649 / 1000000000000) (4097071389 / 1000000000000)
      | 6 => orderedInterval (-5192697466 / 1000000000000) (-5192697396 / 1000000000000)
      | 7 => orderedInterval (1359333700 / 1000000000000) (1359333723 / 1000000000000)
      | _ => orderedInterval (15531479079 / 1000000000000) (15531481815 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17706151521 / 1000000000000) (-17706142580 / 1000000000000)
      | 1 => orderedInterval (-4396918733 / 1000000000000) (-4396917923 / 1000000000000)
      | 2 => orderedInterval (-376681101 / 1000000000000) (-376680778 / 1000000000000)
      | 3 => orderedInterval (15055116153 / 1000000000000) (15055119944 / 1000000000000)
      | 4 => orderedInterval (7295615557 / 1000000000000) (7295615624 / 1000000000000)
      | 5 => orderedInterval (-578725247 / 1000000000000) (-578723000 / 1000000000000)
      | 6 => orderedInterval (843661019 / 1000000000000) (843661083 / 1000000000000)
      | 7 => orderedInterval (-4186797558 / 1000000000000) (-4186797535 / 1000000000000)
      | _ => orderedInterval (14326895436 / 1000000000000) (14326898927 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7055086846 / 1000000000000) (7055095884 / 1000000000000)
      | 1 => orderedInterval (10233010186 / 1000000000000) (10233011438 / 1000000000000)
      | 2 => orderedInterval (9808471367 / 1000000000000) (9808472000 / 1000000000000)
      | 3 => orderedInterval (-139965177801 / 1000000000000) (-139965172257 / 1000000000000)
      | 4 => orderedInterval (-3624980353 / 1000000000000) (-3624980240 / 1000000000000)
      | 5 => orderedInterval (-9192484979 / 1000000000000) (-9192482088 / 1000000000000)
      | 6 => orderedInterval (7338423376 / 1000000000000) (7338423435 / 1000000000000)
      | 7 => orderedInterval (-1129789553 / 1000000000000) (-1129789530 / 1000000000000)
      | _ => orderedInterval (-35658632193 / 1000000000000) (-35658627711 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16767406736 / 1000000000000) (16767415939 / 1000000000000)
      | 1 => orderedInterval (10988372741 / 1000000000000) (10988374705 / 1000000000000)
      | 2 => orderedInterval (5587030901 / 1000000000000) (5587032148 / 1000000000000)
      | 3 => orderedInterval (-54367851725 / 1000000000000) (-54367843087 / 1000000000000)
      | 4 => orderedInterval (-10886537166 / 1000000000000) (-10886536974 / 1000000000000)
      | 5 => orderedInterval (6241757550 / 1000000000000) (6241761297 / 1000000000000)
      | 6 => orderedInterval (-571125182 / 1000000000000) (-571125126 / 1000000000000)
      | 7 => orderedInterval (5264646374 / 1000000000000) (5264646398 / 1000000000000)
      | _ => orderedInterval (-31893164046 / 1000000000000) (-31893158182 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4426037840 / 1000000000000) (4426052879 / 1000000000000)
    | 1 => orderedInterval (31524919587 / 1000000000000) (31524936434 / 1000000000000)
    | 2 => orderedInterval (10276014005 / 1000000000000) (10276033762 / 1000000000000)
    | 3 => orderedInterval (-155136073104 / 1000000000000) (-155136049069 / 1000000000000)
    | _ => orderedInterval (-52869463817 / 1000000000000) (-52869432882 / 1000000000000)

theorem compactCertificate310_stateChecks0 :
    compactCertificate310.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (367 / 2)) (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (540661077879667 / 4000000000000)) (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (174838684003411 / 800000000000)) (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks1 :
    compactCertificate310.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (157763554097369 / 4000000000000)) (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (423775097585093 / 4000000000000)) (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1150631825940081 / 4000000000000)) (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks2 :
    compactCertificate310.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (847550195170553 / 4000000000000)) (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1452291705455069 / 4000000000000)) (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1069751497093271 / 4000000000000)) (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks3 :
    compactCertificate310.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1641273895484633 / 4000000000000)) (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (947589925371857 / 4000000000000)) (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1681514951187013 / 4000000000000)) (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks4 :
    compactCertificate310.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1571089387781497 / 4000000000000)) (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1121203520032201 / 4000000000000)) (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1271325292755279 / 4000000000000)) (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks5 :
    compactCertificate310.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1059898486774751 / 4000000000000)) (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (936452456561771 / 4000000000000)) (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (271420421899329 / 800000000000)) (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks6 :
    compactCertificate310.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (750763171047763 / 4000000000000)) (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (636430254571643 / 4000000000000)) (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (398248502906729 / 4000000000000)) (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks7 :
    compactCertificate310.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (214179369377943 / 4000000000000)) (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (581538651682829 / 4000000000000)) (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (794041311604333 / 4000000000000)) (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_stateChecks8 :
    compactCertificate310.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (335751497093271 / 4000000000000)) (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1364811195318391 / 4000000000000)) (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911630627575769 / 4000000000000)) (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_states : ∀ j,
    BesselStateValid (compactCertificate310.point j) (compactCertificate310.state j) :=
  compactCertificate310.statesValid_of_checks3 compactCertificate310_stateChecks0
    compactCertificate310_stateChecks1 compactCertificate310_stateChecks2
    compactCertificate310_stateChecks3 compactCertificate310_stateChecks4
    compactCertificate310_stateChecks5 compactCertificate310_stateChecks6
    compactCertificate310_stateChecks7 compactCertificate310_stateChecks8

theorem compactCertificate310_chunkChecks0_0 :
    compactCertificate310.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (367 / 2) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (540661077879667 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (174838684003411 / 800000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000)))) (orderedInterval (18254573771 / 1000000000000) (18254582514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (157763554097369 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (423775097585093 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1150631825940081 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000)))) (orderedInterval (801144081 / 1000000000000) (801144642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (847550195170553 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1452291705455069 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1069751497093271 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000)))) (orderedInterval (-400109938 / 1000000000000) (-400109853 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks0_1 :
    compactCertificate310.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1641273895484633 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (947589925371857 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1681514951187013 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000)))) (orderedInterval (-5351265859 / 1000000000000) (-5351263865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1571089387781497 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1121203520032201 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1271325292755279 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000)))) (orderedInterval (-3720493872 / 1000000000000) (-3720493846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1059898486774751 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (936452456561771 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (271420421899329 / 800000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000)))) (orderedInterval (-658518671 / 1000000000000) (-658517315 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks0_2 :
    compactCertificate310.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (750763171047763 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (636430254571643 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (398248502906729 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000)))) (orderedInterval (-1448453630 / 1000000000000) (-1448453552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (214179369377943 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (581538651682829 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (794041311604333 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000)))) (orderedInterval (4363982792 / 1000000000000) (4363982818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (335751497093271 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1364811195318391 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (911630627575769 / 4000000000000) 0 (IntervalRat.scale (367 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000)))) (orderedInterval (-7414820834 / 1000000000000) (-7414818664 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks0 :
    compactCertificate310.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate310.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate310_chunkChecks0_0
    compactCertificate310_chunkChecks0_1 compactCertificate310_chunkChecks0_2

theorem compactCertificate310_chunkChecks1_0 :
    compactCertificate310.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (367 / 2) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (540661077879667 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (174838684003411 / 800000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000)))) (orderedInterval (-8422438100 / 1000000000000) (-8422429289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (157763554097369 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (423775097585093 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1150631825940081 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000)))) (orderedInterval (-2507481998 / 1000000000000) (-2507481438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (847550195170553 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1452291705455069 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1069751497093271 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000)))) (orderedInterval (-2797621561 / 1000000000000) (-2797621397 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks1_1 :
    compactCertificate310.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1641273895484633 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (947589925371857 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1681514951187013 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000)))) (orderedInterval (28927276266 / 1000000000000) (28927278968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1571089387781497 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1121203520032201 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1271325292755279 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000)))) (orderedInterval (530000018 / 1000000000000) (530000059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1059898486774751 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (936452456561771 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (271420421899329 / 800000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000)))) (orderedInterval (4097069649 / 1000000000000) (4097071389 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks1_2 :
    compactCertificate310.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (750763171047763 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (636430254571643 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (398248502906729 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000)))) (orderedInterval (-5192697466 / 1000000000000) (-5192697396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (214179369377943 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (581538651682829 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (794041311604333 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000)))) (orderedInterval (1359333700 / 1000000000000) (1359333723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (335751497093271 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1364811195318391 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (911630627575769 / 4000000000000) 1 (IntervalRat.scale (367 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000)))) (orderedInterval (15531479079 / 1000000000000) (15531481815 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks1 :
    compactCertificate310.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate310.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate310_chunkChecks1_0
    compactCertificate310_chunkChecks1_1 compactCertificate310_chunkChecks1_2

theorem compactCertificate310_chunkChecks2_0 :
    compactCertificate310.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (367 / 2) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (540661077879667 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (174838684003411 / 800000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000)))) (orderedInterval (-17706151521 / 1000000000000) (-17706142580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (157763554097369 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (423775097585093 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1150631825940081 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000)))) (orderedInterval (-4396918733 / 1000000000000) (-4396917923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (847550195170553 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1452291705455069 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1069751497093271 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000)))) (orderedInterval (-376681101 / 1000000000000) (-376680778 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks2_1 :
    compactCertificate310.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1641273895484633 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (947589925371857 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1681514951187013 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000)))) (orderedInterval (15055116153 / 1000000000000) (15055119944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1571089387781497 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1121203520032201 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1271325292755279 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000)))) (orderedInterval (7295615557 / 1000000000000) (7295615624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1059898486774751 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (936452456561771 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (271420421899329 / 800000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000)))) (orderedInterval (-578725247 / 1000000000000) (-578723000 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks2_2 :
    compactCertificate310.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (750763171047763 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (636430254571643 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (398248502906729 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000)))) (orderedInterval (843661019 / 1000000000000) (843661083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (214179369377943 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (581538651682829 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (794041311604333 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000)))) (orderedInterval (-4186797558 / 1000000000000) (-4186797535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (335751497093271 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1364811195318391 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (911630627575769 / 4000000000000) 2 (IntervalRat.scale (367 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000)))) (orderedInterval (14326895436 / 1000000000000) (14326898927 / 1000000000000))) = true
  rfl'

theorem compactCertificate310_chunkChecks2 :
    compactCertificate310.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate310.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate310_chunkChecks2_0
    compactCertificate310_chunkChecks2_1 compactCertificate310_chunkChecks2_2

theorem compactCertificate310_chunkChecks3_0 :
    compactCertificate310.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (367 / 2) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (540661077879667 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (174838684003411 / 800000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000)))) (orderedInterval (7055086846 / 1000000000000) (7055095884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (157763554097369 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (423775097585093 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1150631825940081 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000)))) (orderedInterval (10233010186 / 1000000000000) (10233011438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (847550195170553 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1452291705455069 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1069751497093271 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000)))) (orderedInterval (9808471367 / 1000000000000) (9808472000 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate310_chunkChecks3_1 :
    compactCertificate310.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1641273895484633 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (947589925371857 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1681514951187013 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000)))) (orderedInterval (-139965177801 / 1000000000000) (-139965172257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1571089387781497 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1121203520032201 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1271325292755279 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000)))) (orderedInterval (-3624980353 / 1000000000000) (-3624980240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1059898486774751 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (936452456561771 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (271420421899329 / 800000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000)))) (orderedInterval (-9192484979 / 1000000000000) (-9192482088 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate310_chunkChecks3_2 :
    compactCertificate310.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (750763171047763 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (636430254571643 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (398248502906729 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000)))) (orderedInterval (7338423376 / 1000000000000) (7338423435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (214179369377943 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (581538651682829 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (794041311604333 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000)))) (orderedInterval (-1129789553 / 1000000000000) (-1129789530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (335751497093271 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1364811195318391 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (911630627575769 / 4000000000000) 3 (IntervalRat.scale (367 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000)))) (orderedInterval (-35658632193 / 1000000000000) (-35658627711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate310_chunkChecks3 :
    compactCertificate310.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate310.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate310_chunkChecks3_0
    compactCertificate310_chunkChecks3_1 compactCertificate310_chunkChecks3_2

theorem compactCertificate310_chunkChecks4_0 :
    compactCertificate310.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (367 / 2) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51646567748 / 1000000000000) (51646588893 / 1000000000000), orderedInterval (-28459307797 / 1000000000000) (-28459286652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (540661077879667 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52066100429 / 1000000000000) (-52066100428 / 1000000000000), orderedInterval (-44518164191 / 1000000000000) (-44518164190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (174838684003411 / 800000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29501175996 / 1000000000000) (-29501170052 / 1000000000000), orderedInterval (45262963698 / 1000000000000) (45262969642 / 1000000000000)))) (orderedInterval (16767406736 / 1000000000000) (16767415939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (157763554097369 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73566380667 / 1000000000000) (73566401635 / 1000000000000), orderedInterval (-104515891842 / 1000000000000) (-104515870874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (423775097585093 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6670455168 / 1000000000000) (-6670455144 / 1000000000000), orderedInterval (77262337128 / 1000000000000) (77262337152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1150631825940081 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25922731356 / 1000000000000) (-25922727001 / 1000000000000), orderedInterval (39302248193 / 1000000000000) (39302252548 / 1000000000000)))) (orderedInterval (10988372741 / 1000000000000) (10988374705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (847550195170553 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44774812691 / 1000000000000) (-44774745967 / 1000000000000), orderedInterval (31724182146 / 1000000000000) (31724248870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1452291705455069 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22482401447 / 1000000000000) (-22482399052 / 1000000000000), orderedInterval (35357488240 / 1000000000000) (35357490634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1069751497093271 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45248090421 / 1000000000000) (-45248090420 / 1000000000000), orderedInterval (-18164984601 / 1000000000000) (-18164984600 / 1000000000000)))) (orderedInterval (5587030901 / 1000000000000) (5587032148 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate310_chunkChecks4_1 :
    compactCertificate310.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1641273895484633 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16957974119 / 1000000000000) (16957974543 / 1000000000000), orderedInterval (-35572792669 / 1000000000000) (-35572792244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (947589925371857 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45688059891 / 1000000000000) (-45688034987 / 1000000000000), orderedInterval (24589697243 / 1000000000000) (24589722147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1681514951187013 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7365651604 / 1000000000000) (7365651605 / 1000000000000), orderedInterval (38203068825 / 1000000000000) (38203068826 / 1000000000000)))) (orderedInterval (-54367851725 / 1000000000000) (-54367843087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1571089387781497 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30466927693 / 1000000000000) (-30466927692 / 1000000000000), orderedInterval (-26278560974 / 1000000000000) (-26278560973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1121203520032201 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47478039436 / 1000000000000) (-47478039401 / 1000000000000), orderedInterval (-4042498155 / 1000000000000) (-4042498120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1271325292755279 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43304073460 / 1000000000000) (-43304073457 / 1000000000000), orderedInterval (-11235259747 / 1000000000000) (-11235259743 / 1000000000000)))) (orderedInterval (-10886537166 / 1000000000000) (-10886536974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1059898486774751 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46899019123 / 1000000000000) (46899023146 / 1000000000000), orderedInterval (-14337958693 / 1000000000000) (-14337954670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (936452456561771 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34442330268 / 1000000000000) (34442352826 / 1000000000000), orderedInterval (-39227224803 / 1000000000000) (-39227202245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (271420421899329 / 800000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30109742549 / 1000000000000) (30109742550 / 1000000000000), orderedInterval (31097444441 / 1000000000000) (31097444442 / 1000000000000)))) (orderedInterval (6241757550 / 1000000000000) (6241761297 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate310_chunkChecks4_2 :
    compactCertificate310.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (750763171047763 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1166708225 / 1000000000000) (-1166708221 / 1000000000000), orderedInterval (58231149819 / 1000000000000) (58231149824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (636430254571643 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20440370719 / 1000000000000) (20440371206 / 1000000000000), orderedInterval (-59925724118 / 1000000000000) (-59925723631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (398248502906729 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14685097309 / 1000000000000) (-14685097203 / 1000000000000), orderedInterval (78677940811 / 1000000000000) (78677940918 / 1000000000000)))) (orderedInterval (-571125182 / 1000000000000) (-571125126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (214179369377943 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86804475721 / 1000000000000) (-86804475720 / 1000000000000), orderedInterval (-65176718749 / 1000000000000) (-65176718748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (581538651682829 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (65933086240 / 1000000000000) (65933086394 / 1000000000000), orderedInterval (-5854125140 / 1000000000000) (-5854124986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (794041311604333 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55545480190 / 1000000000000) (-55545480187 / 1000000000000), orderedInterval (-10890774029 / 1000000000000) (-10890774026 / 1000000000000)))) (orderedInterval (5264646374 / 1000000000000) (5264646398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (335751497093271 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (8799832977 / 1000000000000) (8799833012 / 1000000000000), orderedInterval (-86696002392 / 1000000000000) (-86696002357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1364811195318391 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18623591060 / 1000000000000) (18623591723 / 1000000000000), orderedInterval (-39001303519 / 1000000000000) (-39001302856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (911630627575769 / 4000000000000) 4 (IntervalRat.scale (367 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31721919381 / 1000000000000) (31721930381 / 1000000000000), orderedInterval (-42343049863 / 1000000000000) (-42343038863 / 1000000000000)))) (orderedInterval (-31893164046 / 1000000000000) (-31893158182 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate310_chunkChecks4 :
    compactCertificate310.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate310.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate310_chunkChecks4_0
    compactCertificate310_chunkChecks4_1 compactCertificate310_chunkChecks4_2

theorem compactCertificate310_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate310.chunkCheck r b = true :=
  compactCertificate310.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate310_chunkChecks0
    · exact compactCertificate310_chunkChecks1
    · exact compactCertificate310_chunkChecks2
    · exact compactCertificate310_chunkChecks3
    · exact compactCertificate310_chunkChecks4)

theorem compactCertificate310_coefficient0 :
    compactCertificate310.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate310_coefficient1 :
    compactCertificate310.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate310_coefficient2 :
    compactCertificate310.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate310_coefficient3 :
    compactCertificate310.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate310_coefficient4 :
    compactCertificate310.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate310_coefficients : ∀ r : Fin 5,
    compactCertificate310.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate310_coefficient0
  · exact compactCertificate310_coefficient1
  · exact compactCertificate310_coefficient2
  · exact compactCertificate310_coefficient3
  · exact compactCertificate310_coefficient4

theorem compactCertificate310_lower : (1 : ℚ) ≤ compactCertificate310.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate310, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate310_proves {t : ℝ} (ht : t ∈ compactCertificate310.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate310.proves compactCertificate310_states compactCertificate310_chunks
    compactCertificate310_coefficients compactCertificate310_lower ht

end Erdos232
