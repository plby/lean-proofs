/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate567 : CompactCertificate where
  left := 438
  right := 439
  center := 877 / 2
  grid := fun i =>
    match i.val with
    | 0 => 140
    | 1 => 103
    | 2 => 166
    | 3 => 30
    | 4 => 81
    | 5 => 219
    | 6 => 161
    | 7 => 276
    | 8 => 204
    | 9 => 312
    | 10 => 180
    | 11 => 320
    | 12 => 299
    | 13 => 213
    | 14 => 242
    | 15 => 202
    | 16 => 178
    | 17 => 258
    | 18 => 143
    | 19 => 121
    | 20 => 76
    | 21 => 41
    | 22 => 111
    | 23 => 151
    | 24 => 64
    | 25 => 260
    | _ => 173
  point := fun i =>
    match i.val with
    | 0 => 877 / 2
    | 1 => 1291988461309177 / 4000000000000
    | 2 => 417802522809241 / 800000000000
    | 3 => 376999010744939 / 4000000000000
    | 4 => 1012672372158383 / 4000000000000
    | 5 => 2749602483241011 / 4000000000000
    | 6 => 2025344744317643 / 4000000000000
    | 7 => 3470462740283639 / 4000000000000
    | 8 => 2556327147004901 / 4000000000000
    | 9 => 3922063232534123 / 4000000000000
    | 10 => 2264404263082067 / 4000000000000
    | 11 => 4018225101337903 / 4000000000000
    | 12 => 3754347120120907 / 4000000000000
    | 13 => 2679279256316731 / 4000000000000
    | 14 => 3038017116475149 / 4000000000000
    | 15 => 2532781942510781 / 4000000000000
    | 16 => 2237789657778401 / 4000000000000
    | 17 => 648598664865699 / 800000000000
    | 18 => 1794058040896153 / 4000000000000
    | 19 => 1520842869916433 / 4000000000000
    | 20 => 951672852995099 / 4000000000000
    | 21 => 511812825461733 / 4000000000000
    | 22 => 1389671382904199 / 4000000000000
    | 23 => 1897477466694823 / 4000000000000
    | 24 => 802327147004901 / 4000000000000
    | 25 => 3261415308703621 / 4000000000000
    | _ => 2178474278975339 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))
    | 1 => (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))
    | 2 => (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000))
    | 3 => (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))
    | 4 => (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))
    | 5 => (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000))
    | 6 => (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))
    | 7 => (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))
    | 8 => (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000))
    | 9 => (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))
    | 10 => (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))
    | 11 => (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000))
    | 12 => (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))
    | 13 => (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))
    | 14 => (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000))
    | 15 => (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))
    | 16 => (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))
    | 17 => (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000))
    | 18 => (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))
    | 19 => (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))
    | 20 => (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000))
    | 21 => (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))
    | 22 => (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))
    | 23 => (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000))
    | 24 => (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))
    | 25 => (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))
    | _ => (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-5771015922 / 1000000000000) (-5771015429 / 1000000000000)
      | 1 => orderedInterval (653515729 / 1000000000000) (653515874 / 1000000000000)
      | 2 => orderedInterval (-1458787299 / 1000000000000) (-1458786018 / 1000000000000)
      | 3 => orderedInterval (-1521071199 / 1000000000000) (-1521071013 / 1000000000000)
      | 4 => orderedInterval (-2879222173 / 1000000000000) (-2879222090 / 1000000000000)
      | 5 => orderedInterval (-1262368137 / 1000000000000) (-1262368084 / 1000000000000)
      | 6 => orderedInterval (1974662551 / 1000000000000) (1974662662 / 1000000000000)
      | 7 => orderedInterval (1397047455 / 1000000000000) (1397047541 / 1000000000000)
      | _ => orderedInterval (7576437172 / 1000000000000) (7576442061 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12767955429 / 1000000000000) (12767955930 / 1000000000000)
      | 1 => orderedInterval (2282787157 / 1000000000000) (2282787270 / 1000000000000)
      | 2 => orderedInterval (177393004 / 1000000000000) (177394882 / 1000000000000)
      | 3 => orderedInterval (4369568610 / 1000000000000) (4369568991 / 1000000000000)
      | 4 => orderedInterval (200091411 / 1000000000000) (200091542 / 1000000000000)
      | 5 => orderedInterval (-124665359 / 1000000000000) (-124665283 / 1000000000000)
      | 6 => orderedInterval (8368647517 / 1000000000000) (8368647620 / 1000000000000)
      | 7 => orderedInterval (3219607902 / 1000000000000) (3219607976 / 1000000000000)
      | _ => orderedInterval (-5799858924 / 1000000000000) (-5799852804 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (4847865271 / 1000000000000) (4847865784 / 1000000000000)
      | 1 => orderedInterval (-1213537823 / 1000000000000) (-1213537709 / 1000000000000)
      | 2 => orderedInterval (4548074321 / 1000000000000) (4548077083 / 1000000000000)
      | 3 => orderedInterval (15728066564 / 1000000000000) (15728067375 / 1000000000000)
      | 4 => orderedInterval (6682203893 / 1000000000000) (6682204104 / 1000000000000)
      | 5 => orderedInterval (1069535333 / 1000000000000) (1069535446 / 1000000000000)
      | 6 => orderedInterval (-1640240693 / 1000000000000) (-1640240596 / 1000000000000)
      | 7 => orderedInterval (-1996889070 / 1000000000000) (-1996889003 / 1000000000000)
      | _ => orderedInterval (-14259958769 / 1000000000000) (-14259951060 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12952220660 / 1000000000000) (-12952220136 / 1000000000000)
      | 1 => orderedInterval (-7886998985 / 1000000000000) (-7886998842 / 1000000000000)
      | 2 => orderedInterval (341937259 / 1000000000000) (341941327 / 1000000000000)
      | 3 => orderedInterval (-22104740511 / 1000000000000) (-22104738739 / 1000000000000)
      | 4 => orderedInterval (-2574011571 / 1000000000000) (-2574011224 / 1000000000000)
      | 5 => orderedInterval (-1273246352 / 1000000000000) (-1273246180 / 1000000000000)
      | 6 => orderedInterval (-7681878023 / 1000000000000) (-7681877928 / 1000000000000)
      | 7 => orderedInterval (-2987880480 / 1000000000000) (-2987880415 / 1000000000000)
      | _ => orderedInterval (15502320920 / 1000000000000) (15502330672 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-3582333495 / 1000000000000) (-3582332954 / 1000000000000)
      | 1 => orderedInterval (2436001589 / 1000000000000) (2436001791 / 1000000000000)
      | 2 => orderedInterval (-15339008661 / 1000000000000) (-15339002641 / 1000000000000)
      | 3 => orderedInterval (-92042262940 / 1000000000000) (-92042259020 / 1000000000000)
      | 4 => orderedInterval (-15414621490 / 1000000000000) (-15414620910 / 1000000000000)
      | 5 => orderedInterval (1764326642 / 1000000000000) (1764326910 / 1000000000000)
      | 6 => orderedInterval (1363178045 / 1000000000000) (1363178138 / 1000000000000)
      | 7 => orderedInterval (2512698074 / 1000000000000) (2512698138 / 1000000000000)
      | _ => orderedInterval (31328614796 / 1000000000000) (31328627256 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-1290801823 / 1000000000000) (-1290794496 / 1000000000000)
    | 1 => orderedInterval (25461526747 / 1000000000000) (25461536124 / 1000000000000)
    | 2 => orderedInterval (13765119027 / 1000000000000) (13765131424 / 1000000000000)
    | 3 => orderedInterval (-41616718403 / 1000000000000) (-41616701465 / 1000000000000)
    | _ => orderedInterval (-86973407440 / 1000000000000) (-86973383292 / 1000000000000)

theorem compactCertificate567_stateChecks0 :
    compactCertificate567.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (877 / 2)) (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1291988461309177 / 4000000000000)) (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (417802522809241 / 800000000000)) (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks1 :
    compactCertificate567.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (376999010744939 / 4000000000000)) (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1012672372158383 / 4000000000000)) (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2749602483241011 / 4000000000000)) (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks2 :
    compactCertificate567.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2025344744317643 / 4000000000000)) (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3470462740283639 / 4000000000000)) (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2556327147004901 / 4000000000000)) (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks3 :
    compactCertificate567.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 312 12 (3922063232534123 / 4000000000000)) (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2264404263082067 / 4000000000000)) (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 320 12 (4018225101337903 / 4000000000000)) (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks4 :
    compactCertificate567.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 299 12 (3754347120120907 / 4000000000000)) (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2679279256316731 / 4000000000000)) (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3038017116475149 / 4000000000000)) (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks5 :
    compactCertificate567.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2532781942510781 / 4000000000000)) (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2237789657778401 / 4000000000000)) (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (648598664865699 / 800000000000)) (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks6 :
    compactCertificate567.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1794058040896153 / 4000000000000)) (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1520842869916433 / 4000000000000)) (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (951672852995099 / 4000000000000)) (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks7 :
    compactCertificate567.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (511812825461733 / 4000000000000)) (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1389671382904199 / 4000000000000)) (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1897477466694823 / 4000000000000)) (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_stateChecks8 :
    compactCertificate567.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (802327147004901 / 4000000000000)) (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3261415308703621 / 4000000000000)) (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2178474278975339 / 4000000000000)) (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_states : ∀ j,
    BesselStateValid (compactCertificate567.point j) (compactCertificate567.state j) :=
  compactCertificate567.statesValid_of_checks3 compactCertificate567_stateChecks0
    compactCertificate567_stateChecks1 compactCertificate567_stateChecks2
    compactCertificate567_stateChecks3 compactCertificate567_stateChecks4
    compactCertificate567_stateChecks5 compactCertificate567_stateChecks6
    compactCertificate567_stateChecks7 compactCertificate567_stateChecks8

theorem compactCertificate567_chunkChecks0_0 :
    compactCertificate567.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (877 / 2) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1291988461309177 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (417802522809241 / 800000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000)))) (orderedInterval (-5771015922 / 1000000000000) (-5771015429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (376999010744939 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1012672372158383 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2749602483241011 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000)))) (orderedInterval (653515729 / 1000000000000) (653515874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2025344744317643 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3470462740283639 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2556327147004901 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000)))) (orderedInterval (-1458787299 / 1000000000000) (-1458786018 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks0_1 :
    compactCertificate567.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3922063232534123 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2264404263082067 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4018225101337903 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000)))) (orderedInterval (-1521071199 / 1000000000000) (-1521071013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3754347120120907 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2679279256316731 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3038017116475149 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000)))) (orderedInterval (-2879222173 / 1000000000000) (-2879222090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2532781942510781 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2237789657778401 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (648598664865699 / 800000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000)))) (orderedInterval (-1262368137 / 1000000000000) (-1262368084 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks0_2 :
    compactCertificate567.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1794058040896153 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1520842869916433 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (951672852995099 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000)))) (orderedInterval (1974662551 / 1000000000000) (1974662662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (511812825461733 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1389671382904199 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1897477466694823 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000)))) (orderedInterval (1397047455 / 1000000000000) (1397047541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (802327147004901 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3261415308703621 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2178474278975339 / 4000000000000) 0 (IntervalRat.scale (877 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000)))) (orderedInterval (7576437172 / 1000000000000) (7576442061 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks0 :
    compactCertificate567.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate567.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate567_chunkChecks0_0
    compactCertificate567_chunkChecks0_1 compactCertificate567_chunkChecks0_2

theorem compactCertificate567_chunkChecks1_0 :
    compactCertificate567.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (877 / 2) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1291988461309177 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (417802522809241 / 800000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000)))) (orderedInterval (12767955429 / 1000000000000) (12767955930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (376999010744939 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1012672372158383 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2749602483241011 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000)))) (orderedInterval (2282787157 / 1000000000000) (2282787270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2025344744317643 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3470462740283639 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2556327147004901 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000)))) (orderedInterval (177393004 / 1000000000000) (177394882 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks1_1 :
    compactCertificate567.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3922063232534123 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2264404263082067 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4018225101337903 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000)))) (orderedInterval (4369568610 / 1000000000000) (4369568991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3754347120120907 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2679279256316731 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3038017116475149 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000)))) (orderedInterval (200091411 / 1000000000000) (200091542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2532781942510781 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2237789657778401 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (648598664865699 / 800000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000)))) (orderedInterval (-124665359 / 1000000000000) (-124665283 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks1_2 :
    compactCertificate567.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1794058040896153 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1520842869916433 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (951672852995099 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000)))) (orderedInterval (8368647517 / 1000000000000) (8368647620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (511812825461733 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1389671382904199 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1897477466694823 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000)))) (orderedInterval (3219607902 / 1000000000000) (3219607976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (802327147004901 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3261415308703621 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2178474278975339 / 4000000000000) 1 (IntervalRat.scale (877 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000)))) (orderedInterval (-5799858924 / 1000000000000) (-5799852804 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks1 :
    compactCertificate567.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate567.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate567_chunkChecks1_0
    compactCertificate567_chunkChecks1_1 compactCertificate567_chunkChecks1_2

theorem compactCertificate567_chunkChecks2_0 :
    compactCertificate567.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (877 / 2) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1291988461309177 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (417802522809241 / 800000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000)))) (orderedInterval (4847865271 / 1000000000000) (4847865784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (376999010744939 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1012672372158383 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2749602483241011 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000)))) (orderedInterval (-1213537823 / 1000000000000) (-1213537709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2025344744317643 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3470462740283639 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2556327147004901 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000)))) (orderedInterval (4548074321 / 1000000000000) (4548077083 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks2_1 :
    compactCertificate567.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3922063232534123 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2264404263082067 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4018225101337903 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000)))) (orderedInterval (15728066564 / 1000000000000) (15728067375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3754347120120907 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2679279256316731 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3038017116475149 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000)))) (orderedInterval (6682203893 / 1000000000000) (6682204104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2532781942510781 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2237789657778401 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (648598664865699 / 800000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000)))) (orderedInterval (1069535333 / 1000000000000) (1069535446 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks2_2 :
    compactCertificate567.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1794058040896153 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1520842869916433 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (951672852995099 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000)))) (orderedInterval (-1640240693 / 1000000000000) (-1640240596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (511812825461733 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1389671382904199 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1897477466694823 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000)))) (orderedInterval (-1996889070 / 1000000000000) (-1996889003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (802327147004901 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3261415308703621 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2178474278975339 / 4000000000000) 2 (IntervalRat.scale (877 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000)))) (orderedInterval (-14259958769 / 1000000000000) (-14259951060 / 1000000000000))) = true
  rfl'

theorem compactCertificate567_chunkChecks2 :
    compactCertificate567.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate567.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate567_chunkChecks2_0
    compactCertificate567_chunkChecks2_1 compactCertificate567_chunkChecks2_2

theorem compactCertificate567_chunkChecks3_0 :
    compactCertificate567.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (877 / 2) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1291988461309177 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (417802522809241 / 800000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000)))) (orderedInterval (-12952220660 / 1000000000000) (-12952220136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (376999010744939 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1012672372158383 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2749602483241011 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000)))) (orderedInterval (-7886998985 / 1000000000000) (-7886998842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2025344744317643 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3470462740283639 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2556327147004901 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000)))) (orderedInterval (341937259 / 1000000000000) (341941327 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate567_chunkChecks3_1 :
    compactCertificate567.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3922063232534123 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2264404263082067 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4018225101337903 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000)))) (orderedInterval (-22104740511 / 1000000000000) (-22104738739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3754347120120907 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2679279256316731 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3038017116475149 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000)))) (orderedInterval (-2574011571 / 1000000000000) (-2574011224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2532781942510781 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2237789657778401 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (648598664865699 / 800000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000)))) (orderedInterval (-1273246352 / 1000000000000) (-1273246180 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate567_chunkChecks3_2 :
    compactCertificate567.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1794058040896153 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1520842869916433 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (951672852995099 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000)))) (orderedInterval (-7681878023 / 1000000000000) (-7681877928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (511812825461733 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1389671382904199 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1897477466694823 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000)))) (orderedInterval (-2987880480 / 1000000000000) (-2987880415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (802327147004901 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3261415308703621 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2178474278975339 / 4000000000000) 3 (IntervalRat.scale (877 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000)))) (orderedInterval (15502320920 / 1000000000000) (15502330672 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate567_chunkChecks3 :
    compactCertificate567.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate567.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate567_chunkChecks3_0
    compactCertificate567_chunkChecks3_1 compactCertificate567_chunkChecks3_2

theorem compactCertificate567_chunkChecks4_0 :
    compactCertificate567.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (877 / 2) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19519907175 / 1000000000000) (-19519906065 / 1000000000000), orderedInterval (32745126262 / 1000000000000) (32745127371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1291988461309177 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8736636650 / 1000000000000) (-8736636649 / 1000000000000), orderedInterval (-43514053273 / 1000000000000) (-43514053272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (417802522809241 / 800000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34890264033 / 1000000000000) (34890264414 / 1000000000000), orderedInterval (1253391772 / 1000000000000) (1253392153 / 1000000000000)))) (orderedInterval (-3582333495 / 1000000000000) (-3582332954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (376999010744939 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (58151732656 / 1000000000000) (58151732657 / 1000000000000), orderedInterval (57768873116 / 1000000000000) (57768873117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1012672372158383 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24742541537 / 1000000000000) (24742544064 / 1000000000000), orderedInterval (-43665630482 / 1000000000000) (-43665627955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2749602483241011 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5359816533 / 1000000000000) (-5359816532 / 1000000000000), orderedInterval (-29952717783 / 1000000000000) (-29952717782 / 1000000000000)))) (orderedInterval (2436001589 / 1000000000000) (2436001791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2025344744317643 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34392074311 / 1000000000000) (-34392074294 / 1000000000000), orderedInterval (-8596865289 / 1000000000000) (-8596865272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3470462740283639 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26249681186 / 1000000000000) (26249681420 / 1000000000000), orderedInterval (6671569631 / 1000000000000) (6671569865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2556327147004901 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26859539958 / 1000000000000) (-26859488275 / 1000000000000), orderedInterval (16595483452 / 1000000000000) (16595535134 / 1000000000000)))) (orderedInterval (-15339008661 / 1000000000000) (-15339002641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate567_chunkChecks4_1 :
    compactCertificate567.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3922063232534123 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22981365789 / 1000000000000) (22981365821 / 1000000000000), orderedInterval (10994054538 / 1000000000000) (10994054571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2264404263082067 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33044172035 / 1000000000000) (33044172119 / 1000000000000), orderedInterval (5684953681 / 1000000000000) (5684953765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4018225101337903 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (802913539 / 1000000000000) (802913540 / 1000000000000), orderedInterval (25160834865 / 1000000000000) (25160834866 / 1000000000000)))) (orderedInterval (-92042262940 / 1000000000000) (-92042259020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3754347120120907 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-933248093 / 1000000000000) (-933248092 / 1000000000000), orderedInterval (-26026488007 / 1000000000000) (-26026488006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2679279256316731 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30588549743 / 1000000000000) (-30588549422 / 1000000000000), orderedInterval (-3820960025 / 1000000000000) (-3820959703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3038017116475149 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (697395747 / 1000000000000) (697395748 / 1000000000000), orderedInterval (28942901898 / 1000000000000) (28942901899 / 1000000000000)))) (orderedInterval (-15414621490 / 1000000000000) (-15414620910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2532781942510781 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18450120175 / 1000000000000) (-18450119252 / 1000000000000), orderedInterval (25802184383 / 1000000000000) (25802185306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2237789657778401 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28903927878 / 1000000000000) (28903927879 / 1000000000000), orderedInterval (17366885463 / 1000000000000) (17366885464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (648598664865699 / 800000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23619930824 / 1000000000000) (23619930826 / 1000000000000), orderedInterval (15062690933 / 1000000000000) (15062690935 / 1000000000000)))) (orderedInterval (1764326642 / 1000000000000) (1764326910 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate567_chunkChecks4_2 :
    compactCertificate567.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1794058040896153 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1953703735 / 1000000000000) (-1953703734 / 1000000000000), orderedInterval (-37622017390 / 1000000000000) (-37622017389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1520842869916433 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31092319974 / 1000000000000) (-31092319973 / 1000000000000), orderedInterval (-26560881000 / 1000000000000) (-26560880999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (951672852995099 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2996252039 / 1000000000000) (-2996252033 / 1000000000000), orderedInterval (51647567583 / 1000000000000) (51647567589 / 1000000000000)))) (orderedInterval (1363178045 / 1000000000000) (1363178138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (511812825461733 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4769632304 / 1000000000000) (4769632319 / 1000000000000), orderedInterval (-70394053383 / 1000000000000) (-70394053367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1389671382904199 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (21042913356 / 1000000000000) (21042914794 / 1000000000000), orderedInterval (-37308017420 / 1000000000000) (-37308015983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1897477466694823 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25607332209 / 1000000000000) (-25607332208 / 1000000000000), orderedInterval (-26170307760 / 1000000000000) (-26170307759 / 1000000000000)))) (orderedInterval (2512698074 / 1000000000000) (2512698138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (802327147004901 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16897832211 / 1000000000000) (16897832212 / 1000000000000), orderedInterval (53701134978 / 1000000000000) (53701134979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3261415308703621 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17461652586 / 1000000000000) (-17461652008 / 1000000000000), orderedInterval (21825388815 / 1000000000000) (21825389394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2178474278975339 / 4000000000000) 4 (IntervalRat.scale (877 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32261785538 / 1000000000000) (-32261760381 / 1000000000000), orderedInterval (11347970217 / 1000000000000) (11347995374 / 1000000000000)))) (orderedInterval (31328614796 / 1000000000000) (31328627256 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate567_chunkChecks4 :
    compactCertificate567.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate567.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate567_chunkChecks4_0
    compactCertificate567_chunkChecks4_1 compactCertificate567_chunkChecks4_2

theorem compactCertificate567_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate567.chunkCheck r b = true :=
  compactCertificate567.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate567_chunkChecks0
    · exact compactCertificate567_chunkChecks1
    · exact compactCertificate567_chunkChecks2
    · exact compactCertificate567_chunkChecks3
    · exact compactCertificate567_chunkChecks4)

theorem compactCertificate567_coefficient0 :
    compactCertificate567.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate567_coefficient1 :
    compactCertificate567.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate567_coefficient2 :
    compactCertificate567.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate567_coefficient3 :
    compactCertificate567.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate567_coefficient4 :
    compactCertificate567.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate567_coefficients : ∀ r : Fin 5,
    compactCertificate567.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate567_coefficient0
  · exact compactCertificate567_coefficient1
  · exact compactCertificate567_coefficient2
  · exact compactCertificate567_coefficient3
  · exact compactCertificate567_coefficient4

theorem compactCertificate567_lower : (1 : ℚ) ≤ compactCertificate567.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate567, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate567_proves {t : ℝ} (ht : t ∈ compactCertificate567.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate567.proves compactCertificate567_states compactCertificate567_chunks
    compactCertificate567_coefficients compactCertificate567_lower ht

end Erdos232
