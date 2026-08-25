/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate317 : CompactCertificate where
  left := 190
  right := 191
  center := 381 / 2
  grid := fun i =>
    match i.val with
    | 0 => 61
    | 1 => 45
    | 2 => 72
    | 3 => 13
    | 4 => 35
    | 5 => 95
    | 6 => 70
    | 7 => 120
    | 8 => 88
    | 9 => 136
    | 10 => 78
    | 11 => 139
    | 12 => 130
    | 13 => 93
    | 14 => 105
    | 15 => 88
    | 16 => 77
    | 17 => 112
    | 18 => 62
    | 19 => 53
    | 20 => 33
    | 21 => 18
    | 22 => 48
    | 23 => 66
    | 24 => 28
    | 25 => 113
    | _ => 75
  point := fun i =>
    match i.val with
    | 0 => 381 / 2
    | 1 => 561285751150281 / 4000000000000
    | 2 => 181508279578473 / 800000000000
    | 3 => 163781782319067 / 4000000000000
    | 4 => 439940905122399 / 4000000000000
    | 5 => 1194525138101283 / 4000000000000
    | 6 => 879881810245179 / 4000000000000
    | 7 => 1507692478960167 / 4000000000000
    | 8 => 1110559456110453 / 4000000000000
    | 9 => 1703883798854619 / 4000000000000
    | 10 => 983737769936451 / 4000000000000
    | 11 => 1745659935700959 / 4000000000000
    | 12 => 1631021952982971 / 4000000000000
    | 13 => 1163974226518443 / 4000000000000
    | 14 => 1319822715367197 / 4000000000000
    | 15 => 1100330581638093 / 4000000000000
    | 16 => 972175438555953 / 4000000000000
    | 17 => 281774334451347 / 800000000000
    | 18 => 779402638063209 / 4000000000000
    | 19 => 660708247934049 / 4000000000000
    | 20 => 413440543889547 / 4000000000000
    | 21 => 222349699544949 / 4000000000000
    | 22 => 603722687441847 / 4000000000000
    | 23 => 824331715861719 / 4000000000000
    | 24 => 348559456110453 / 4000000000000
    | 25 => 1416874837646613 / 4000000000000
    | _ => 946406727810267 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))
    | 1 => (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))
    | 2 => (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000))
    | 3 => (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))
    | 4 => (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))
    | 5 => (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000))
    | 6 => (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))
    | 7 => (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))
    | 8 => (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000))
    | 9 => (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))
    | 10 => (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))
    | 11 => (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000))
    | 12 => (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))
    | 13 => (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))
    | 14 => (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000))
    | 15 => (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))
    | 16 => (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))
    | 17 => (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000))
    | 18 => (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))
    | 19 => (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))
    | 20 => (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000))
    | 21 => (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))
    | 22 => (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))
    | 23 => (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000))
    | 24 => (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))
    | 25 => (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))
    | _ => (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11167867516 / 1000000000000) (11167867746 / 1000000000000)
      | 1 => orderedInterval (1727758087 / 1000000000000) (1727758110 / 1000000000000)
      | 2 => orderedInterval (235633290 / 1000000000000) (235633588 / 1000000000000)
      | 3 => orderedInterval (4353995447 / 1000000000000) (4353995688 / 1000000000000)
      | 4 => orderedInterval (1755333046 / 1000000000000) (1755333112 / 1000000000000)
      | 5 => orderedInterval (3426794093 / 1000000000000) (3426794557 / 1000000000000)
      | 6 => orderedInterval (-9882182754 / 1000000000000) (-9882182398 / 1000000000000)
      | 7 => orderedInterval (1136025997 / 1000000000000) (1136026187 / 1000000000000)
      | _ => orderedInterval (9537646930 / 1000000000000) (9537647196 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-21628409215 / 1000000000000) (-21628408983 / 1000000000000)
      | 1 => orderedInterval (2007731737 / 1000000000000) (2007731764 / 1000000000000)
      | 2 => orderedInterval (-2538321663 / 1000000000000) (-2538321227 / 1000000000000)
      | 3 => orderedInterval (-24795929033 / 1000000000000) (-24795928534 / 1000000000000)
      | 4 => orderedInterval (-7520616678 / 1000000000000) (-7520616575 / 1000000000000)
      | 5 => orderedInterval (188550559 / 1000000000000) (188551164 / 1000000000000)
      | 6 => orderedInterval (-4722539056 / 1000000000000) (-4722538745 / 1000000000000)
      | 7 => orderedInterval (-5371658688 / 1000000000000) (-5371658488 / 1000000000000)
      | _ => orderedInterval (4269459197 / 1000000000000) (4269459535 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12273835052 / 1000000000000) (-12273834817 / 1000000000000)
      | 1 => orderedInterval (-6016441182 / 1000000000000) (-6016441145 / 1000000000000)
      | 2 => orderedInterval (1004595097 / 1000000000000) (1004595741 / 1000000000000)
      | 3 => orderedInterval (-8474590576 / 1000000000000) (-8474589509 / 1000000000000)
      | 4 => orderedInterval (-3956381750 / 1000000000000) (-3956381589 / 1000000000000)
      | 5 => orderedInterval (-7211840341 / 1000000000000) (-7211839546 / 1000000000000)
      | 6 => orderedInterval (8956327166 / 1000000000000) (8956327441 / 1000000000000)
      | 7 => orderedInterval (-1556863577 / 1000000000000) (-1556863363 / 1000000000000)
      | _ => orderedInterval (-14787937480 / 1000000000000) (-14787937040 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (21344017259 / 1000000000000) (21344017496 / 1000000000000)
      | 1 => orderedInterval (-6794292771 / 1000000000000) (-6794292716 / 1000000000000)
      | 2 => orderedInterval (8767688358 / 1000000000000) (8767689309 / 1000000000000)
      | 3 => orderedInterval (124980802045 / 1000000000000) (124980804370 / 1000000000000)
      | 4 => orderedInterval (20805663420 / 1000000000000) (20805663677 / 1000000000000)
      | 5 => orderedInterval (-2059159041 / 1000000000000) (-2059157996 / 1000000000000)
      | 6 => orderedInterval (4736936735 / 1000000000000) (4736936978 / 1000000000000)
      | 7 => orderedInterval (5294951225 / 1000000000000) (5294951455 / 1000000000000)
      | _ => orderedInterval (-18481114796 / 1000000000000) (-18481114217 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13958826393 / 1000000000000) (13958826635 / 1000000000000)
      | 1 => orderedInterval (16142993424 / 1000000000000) (16142993508 / 1000000000000)
      | 2 => orderedInterval (-8037669257 / 1000000000000) (-8037667844 / 1000000000000)
      | 3 => orderedInterval (17376701913 / 1000000000000) (17376707048 / 1000000000000)
      | 4 => orderedInterval (8467703771 / 1000000000000) (8467704185 / 1000000000000)
      | 5 => orderedInterval (17530232167 / 1000000000000) (17530233554 / 1000000000000)
      | 6 => orderedInterval (-8735013104 / 1000000000000) (-8735012887 / 1000000000000)
      | 7 => orderedInterval (2165889080 / 1000000000000) (2165889330 / 1000000000000)
      | _ => orderedInterval (23062848077 / 1000000000000) (23062848859 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (23458871652 / 1000000000000) (23458873786 / 1000000000000)
    | 1 => orderedInterval (-60111732840 / 1000000000000) (-60111730089 / 1000000000000)
    | 2 => orderedInterval (-44316967695 / 1000000000000) (-44316963827 / 1000000000000)
    | 3 => orderedInterval (158595492434 / 1000000000000) (158595498356 / 1000000000000)
    | _ => orderedInterval (81932512464 / 1000000000000) (81932522388 / 1000000000000)

theorem compactCertificate317_stateChecks0 :
    compactCertificate317.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (381 / 2)) (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (561285751150281 / 4000000000000)) (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181508279578473 / 800000000000)) (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks1 :
    compactCertificate317.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (163781782319067 / 4000000000000)) (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (439940905122399 / 4000000000000)) (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194525138101283 / 4000000000000)) (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks2 :
    compactCertificate317.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (879881810245179 / 4000000000000)) (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1507692478960167 / 4000000000000)) (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1110559456110453 / 4000000000000)) (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks3 :
    compactCertificate317.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1703883798854619 / 4000000000000)) (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (983737769936451 / 4000000000000)) (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1745659935700959 / 4000000000000)) (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks4 :
    compactCertificate317.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1631021952982971 / 4000000000000)) (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163974226518443 / 4000000000000)) (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319822715367197 / 4000000000000)) (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks5 :
    compactCertificate317.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1100330581638093 / 4000000000000)) (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (972175438555953 / 4000000000000)) (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (281774334451347 / 800000000000)) (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks6 :
    compactCertificate317.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (779402638063209 / 4000000000000)) (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (660708247934049 / 4000000000000)) (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413440543889547 / 4000000000000)) (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks7 :
    compactCertificate317.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (222349699544949 / 4000000000000)) (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (603722687441847 / 4000000000000)) (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824331715861719 / 4000000000000)) (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_stateChecks8 :
    compactCertificate317.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (348559456110453 / 4000000000000)) (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1416874837646613 / 4000000000000)) (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (946406727810267 / 4000000000000)) (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_states : ∀ j,
    BesselStateValid (compactCertificate317.point j) (compactCertificate317.state j) :=
  compactCertificate317.statesValid_of_checks3 compactCertificate317_stateChecks0
    compactCertificate317_stateChecks1 compactCertificate317_stateChecks2
    compactCertificate317_stateChecks3 compactCertificate317_stateChecks4
    compactCertificate317_stateChecks5 compactCertificate317_stateChecks6
    compactCertificate317_stateChecks7 compactCertificate317_stateChecks8

theorem compactCertificate317_chunkChecks0_0 :
    compactCertificate317.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (381 / 2) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (561285751150281 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (181508279578473 / 800000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000)))) (orderedInterval (11167867516 / 1000000000000) (11167867746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (163781782319067 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (439940905122399 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1194525138101283 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000)))) (orderedInterval (1727758087 / 1000000000000) (1727758110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (879881810245179 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1507692478960167 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1110559456110453 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000)))) (orderedInterval (235633290 / 1000000000000) (235633588 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks0_1 :
    compactCertificate317.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1703883798854619 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (983737769936451 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1745659935700959 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000)))) (orderedInterval (4353995447 / 1000000000000) (4353995688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1631021952982971 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1163974226518443 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1319822715367197 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000)))) (orderedInterval (1755333046 / 1000000000000) (1755333112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1100330581638093 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (972175438555953 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (281774334451347 / 800000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000)))) (orderedInterval (3426794093 / 1000000000000) (3426794557 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks0_2 :
    compactCertificate317.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (779402638063209 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (660708247934049 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (413440543889547 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000)))) (orderedInterval (-9882182754 / 1000000000000) (-9882182398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (222349699544949 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (603722687441847 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (824331715861719 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000)))) (orderedInterval (1136025997 / 1000000000000) (1136026187 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (348559456110453 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1416874837646613 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (946406727810267 / 4000000000000) 0 (IntervalRat.scale (381 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000)))) (orderedInterval (9537646930 / 1000000000000) (9537647196 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks0 :
    compactCertificate317.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate317.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate317_chunkChecks0_0
    compactCertificate317_chunkChecks0_1 compactCertificate317_chunkChecks0_2

theorem compactCertificate317_chunkChecks1_0 :
    compactCertificate317.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (381 / 2) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (561285751150281 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (181508279578473 / 800000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000)))) (orderedInterval (-21628409215 / 1000000000000) (-21628408983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (163781782319067 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (439940905122399 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1194525138101283 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000)))) (orderedInterval (2007731737 / 1000000000000) (2007731764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (879881810245179 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1507692478960167 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1110559456110453 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000)))) (orderedInterval (-2538321663 / 1000000000000) (-2538321227 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks1_1 :
    compactCertificate317.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1703883798854619 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (983737769936451 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1745659935700959 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000)))) (orderedInterval (-24795929033 / 1000000000000) (-24795928534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1631021952982971 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1163974226518443 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1319822715367197 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000)))) (orderedInterval (-7520616678 / 1000000000000) (-7520616575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1100330581638093 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (972175438555953 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (281774334451347 / 800000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000)))) (orderedInterval (188550559 / 1000000000000) (188551164 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks1_2 :
    compactCertificate317.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (779402638063209 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (660708247934049 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (413440543889547 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000)))) (orderedInterval (-4722539056 / 1000000000000) (-4722538745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (222349699544949 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (603722687441847 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (824331715861719 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000)))) (orderedInterval (-5371658688 / 1000000000000) (-5371658488 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (348559456110453 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1416874837646613 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (946406727810267 / 4000000000000) 1 (IntervalRat.scale (381 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000)))) (orderedInterval (4269459197 / 1000000000000) (4269459535 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks1 :
    compactCertificate317.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate317.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate317_chunkChecks1_0
    compactCertificate317_chunkChecks1_1 compactCertificate317_chunkChecks1_2

theorem compactCertificate317_chunkChecks2_0 :
    compactCertificate317.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (381 / 2) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (561285751150281 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (181508279578473 / 800000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000)))) (orderedInterval (-12273835052 / 1000000000000) (-12273834817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (163781782319067 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (439940905122399 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1194525138101283 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000)))) (orderedInterval (-6016441182 / 1000000000000) (-6016441145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (879881810245179 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1507692478960167 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1110559456110453 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000)))) (orderedInterval (1004595097 / 1000000000000) (1004595741 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks2_1 :
    compactCertificate317.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1703883798854619 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (983737769936451 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1745659935700959 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000)))) (orderedInterval (-8474590576 / 1000000000000) (-8474589509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1631021952982971 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1163974226518443 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1319822715367197 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000)))) (orderedInterval (-3956381750 / 1000000000000) (-3956381589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1100330581638093 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (972175438555953 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (281774334451347 / 800000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000)))) (orderedInterval (-7211840341 / 1000000000000) (-7211839546 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks2_2 :
    compactCertificate317.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (779402638063209 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (660708247934049 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (413440543889547 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000)))) (orderedInterval (8956327166 / 1000000000000) (8956327441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (222349699544949 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (603722687441847 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (824331715861719 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000)))) (orderedInterval (-1556863577 / 1000000000000) (-1556863363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (348559456110453 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1416874837646613 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (946406727810267 / 4000000000000) 2 (IntervalRat.scale (381 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000)))) (orderedInterval (-14787937480 / 1000000000000) (-14787937040 / 1000000000000))) = true
  rfl'

theorem compactCertificate317_chunkChecks2 :
    compactCertificate317.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate317.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate317_chunkChecks2_0
    compactCertificate317_chunkChecks2_1 compactCertificate317_chunkChecks2_2

theorem compactCertificate317_chunkChecks3_0 :
    compactCertificate317.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (381 / 2) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (561285751150281 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (181508279578473 / 800000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000)))) (orderedInterval (21344017259 / 1000000000000) (21344017496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (163781782319067 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (439940905122399 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1194525138101283 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000)))) (orderedInterval (-6794292771 / 1000000000000) (-6794292716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (879881810245179 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1507692478960167 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1110559456110453 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000)))) (orderedInterval (8767688358 / 1000000000000) (8767689309 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate317_chunkChecks3_1 :
    compactCertificate317.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1703883798854619 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (983737769936451 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1745659935700959 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000)))) (orderedInterval (124980802045 / 1000000000000) (124980804370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1631021952982971 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1163974226518443 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1319822715367197 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000)))) (orderedInterval (20805663420 / 1000000000000) (20805663677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1100330581638093 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (972175438555953 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (281774334451347 / 800000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000)))) (orderedInterval (-2059159041 / 1000000000000) (-2059157996 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate317_chunkChecks3_2 :
    compactCertificate317.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (779402638063209 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (660708247934049 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (413440543889547 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000)))) (orderedInterval (4736936735 / 1000000000000) (4736936978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (222349699544949 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (603722687441847 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (824331715861719 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000)))) (orderedInterval (5294951225 / 1000000000000) (5294951455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (348559456110453 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1416874837646613 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (946406727810267 / 4000000000000) 3 (IntervalRat.scale (381 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000)))) (orderedInterval (-18481114796 / 1000000000000) (-18481114217 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate317_chunkChecks3 :
    compactCertificate317.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate317.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate317_chunkChecks3_0
    compactCertificate317_chunkChecks3_1 compactCertificate317_chunkChecks3_2

theorem compactCertificate317_chunkChecks4_0 :
    compactCertificate317.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (381 / 2) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19953220193 / 1000000000000) (19953220729 / 1000000000000), orderedInterval (-54308373319 / 1000000000000) (-54308372783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (561285751150281 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17688251088 / 1000000000000) (17688251332 / 1000000000000), orderedInterval (-65055473480 / 1000000000000) (-65055473237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (181508279578473 / 800000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52730559700 / 1000000000000) (52730559721 / 1000000000000), orderedInterval (4922738414 / 1000000000000) (4922738434 / 1000000000000)))) (orderedInterval (13958826393 / 1000000000000) (13958826635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (163781782319067 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-96661731080 / 1000000000000) (-96661731079 / 1000000000000), orderedInterval (-77587026948 / 1000000000000) (-77587026947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (439940905122399 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55299855777 / 1000000000000) (-55299855776 / 1000000000000), orderedInterval (-51999469073 / 1000000000000) (-51999469072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1194525138101283 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37954068967 / 1000000000000) (-37954068966 / 1000000000000), orderedInterval (-26228649313 / 1000000000000) (-26228649312 / 1000000000000)))) (orderedInterval (16142993424 / 1000000000000) (16142993508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (879881810245179 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40195539932 / 1000000000000) (40195539933 / 1000000000000), orderedInterval (35663811038 / 1000000000000) (35663811039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1507692478960167 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27008229758 / 1000000000000) (27008229759 / 1000000000000), orderedInterval (30940724741 / 1000000000000) (30940724742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1110559456110453 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44218552134 / 1000000000000) (44218563982 / 1000000000000), orderedInterval (-18455875730 / 1000000000000) (-18455863881 / 1000000000000)))) (orderedInterval (-8037669257 / 1000000000000) (-8037667844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate317_chunkChecks4_1 :
    compactCertificate317.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1703883798854619 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18552619180 / 1000000000000) (-18552618414 / 1000000000000), orderedInterval (33938076613 / 1000000000000) (33938077379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (983737769936451 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50601453432 / 1000000000000) (50601453820 / 1000000000000), orderedInterval (-5400304258 / 1000000000000) (-5400303870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1745659935700959 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18935072368 / 1000000000000) (-18935072367 / 1000000000000), orderedInterval (-33147752624 / 1000000000000) (-33147752623 / 1000000000000)))) (orderedInterval (17376701913 / 1000000000000) (17376707048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1631021952982971 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5260696831 / 1000000000000) (5260696832 / 1000000000000), orderedInterval (39154811247 / 1000000000000) (39154811248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1163974226518443 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17764996898 / 1000000000000) (17764997349 / 1000000000000), orderedInterval (-43298901626 / 1000000000000) (-43298901174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1319822715367197 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33671236077 / 1000000000000) (-33671236076 / 1000000000000), orderedInterval (-28156376522 / 1000000000000) (-28156376521 / 1000000000000)))) (orderedInterval (8467703771 / 1000000000000) (8467704185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1100330581638093 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867271117 / 1000000000000) (-26867265997 / 1000000000000), orderedInterval (39954180051 / 1000000000000) (39954185171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (972175438555953 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-47982850675 / 1000000000000) (-47982843931 / 1000000000000), orderedInterval (17903309818 / 1000000000000) (17903316562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (281774334451347 / 800000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38710814993 / 1000000000000) (38710814994 / 1000000000000), orderedInterval (17521495358 / 1000000000000) (17521495359 / 1000000000000)))) (orderedInterval (17530232167 / 1000000000000) (17530233554 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate317_chunkChecks4_2 :
    compactCertificate317.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (779402638063209 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43193536601 / 1000000000000) (43193536602 / 1000000000000), orderedInterval (37326255012 / 1000000000000) (37326255013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (660708247934049 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32062515791 / 1000000000000) (32062521219 / 1000000000000), orderedInterval (-53258780457 / 1000000000000) (-53258775028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (413440543889547 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-35666279454 / 1000000000000) (-35666279453 / 1000000000000), orderedInterval (-69735965372 / 1000000000000) (-69735965371 / 1000000000000)))) (orderedInterval (-8735013104 / 1000000000000) (-8735012887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (222349699544949 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18957967455 / 1000000000000) (-18957967324 / 1000000000000), orderedInterval (105496744288 / 1000000000000) (105496744418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (603722687441847 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51623400902 / 1000000000000) (51623400903 / 1000000000000), orderedInterval (39236851409 / 1000000000000) (39236851410 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (824331715861719 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25537146623 / 1000000000000) (-25537144482 / 1000000000000), orderedInterval (49427968562 / 1000000000000) (49427970703 / 1000000000000)))) (orderedInterval (2165889080 / 1000000000000) (2165889330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (348559456110453 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3483461657 / 1000000000000) (-3483461644 / 1000000000000), orderedInterval (85423201701 / 1000000000000) (85423201715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1416874837646613 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-160453656 / 1000000000000) (-160453655 / 1000000000000), orderedInterval (-42393482961 / 1000000000000) (-42393482959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (946406727810267 / 4000000000000) 4 (IntervalRat.scale (381 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50875457532 / 1000000000000) (-50875456400 / 1000000000000), orderedInterval (10225013579 / 1000000000000) (10225014711 / 1000000000000)))) (orderedInterval (23062848077 / 1000000000000) (23062848859 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate317_chunkChecks4 :
    compactCertificate317.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate317.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate317_chunkChecks4_0
    compactCertificate317_chunkChecks4_1 compactCertificate317_chunkChecks4_2

theorem compactCertificate317_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate317.chunkCheck r b = true :=
  compactCertificate317.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate317_chunkChecks0
    · exact compactCertificate317_chunkChecks1
    · exact compactCertificate317_chunkChecks2
    · exact compactCertificate317_chunkChecks3
    · exact compactCertificate317_chunkChecks4)

theorem compactCertificate317_coefficient0 :
    compactCertificate317.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate317_coefficient1 :
    compactCertificate317.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate317_coefficient2 :
    compactCertificate317.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate317_coefficient3 :
    compactCertificate317.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate317_coefficient4 :
    compactCertificate317.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate317_coefficients : ∀ r : Fin 5,
    compactCertificate317.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate317_coefficient0
  · exact compactCertificate317_coefficient1
  · exact compactCertificate317_coefficient2
  · exact compactCertificate317_coefficient3
  · exact compactCertificate317_coefficient4

theorem compactCertificate317_lower : (1 : ℚ) ≤ compactCertificate317.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate317, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate317_proves {t : ℝ} (ht : t ∈ compactCertificate317.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate317.proves compactCertificate317_states compactCertificate317_chunks
    compactCertificate317_coefficients compactCertificate317_lower ht

end Erdos232
