/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate609 : CompactCertificate where
  left := 480
  right := 481
  center := 961 / 2
  grid := fun i =>
    match i.val with
    | 0 => 153
    | 1 => 113
    | 2 => 182
    | 3 => 33
    | 4 => 88
    | 5 => 240
    | 6 => 177
    | 7 => 303
    | 8 => 223
    | 9 => 342
    | 10 => 198
    | 11 => 351
    | 12 => 328
    | 13 => 234
    | 14 => 265
    | 15 => 221
    | 16 => 195
    | 17 => 283
    | 18 => 157
    | 19 => 133
    | 20 => 83
    | 21 => 45
    | 22 => 121
    | 23 => 166
    | 24 => 70
    | 25 => 285
    | _ => 190
  point := fun i =>
    match i.val with
    | 0 => 961 / 2
    | 1 => 1415736500932861 / 4000000000000
    | 2 => 457820096259613 / 800000000000
    | 3 => 413108380075127 / 4000000000000
    | 4 => 1109667217382219 / 4000000000000
    | 5 => 3012962356208223 / 4000000000000
    | 6 => 2219334434765399 / 4000000000000
    | 7 => 3802867381314227 / 4000000000000
    | 8 => 2801174901107993 / 4000000000000
    | 9 => 4297722652754039 / 4000000000000
    | 10 => 2481291330469631 / 4000000000000
    | 11 => 4403095008421579 / 4000000000000
    | 12 => 4113942511329751 / 4000000000000
    | 13 => 2935903495234183 / 4000000000000
    | 14 => 3329001652146657 / 4000000000000
    | 15 => 2775374511690833 / 4000000000000
    | 16 => 2452127549743493 / 4000000000000
    | 17 => 710722140177807 / 800000000000
    | 18 => 1965894842988829 / 4000000000000
    | 19 => 1666510830090869 / 4000000000000
    | 20 => 1042825098892007 / 4000000000000
    | 21 => 560834806463769 / 4000000000000
    | 22 => 1522775597458307 / 4000000000000
    | 23 => 2079219892239139 / 4000000000000
    | 24 => 879174901107993 / 4000000000000
    | 25 => 3573797162672953 / 4000000000000
    | _ => 2387130880382327 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))
    | 1 => (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))
    | 2 => (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000))
    | 3 => (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))
    | 4 => (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))
    | 5 => (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000))
    | 6 => (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))
    | 7 => (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))
    | 8 => (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000))
    | 9 => (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))
    | 10 => (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))
    | 11 => (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000))
    | 12 => (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))
    | 13 => (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))
    | 14 => (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000))
    | 15 => (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))
    | 16 => (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))
    | 17 => (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000))
    | 18 => (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))
    | 19 => (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))
    | 20 => (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000))
    | 21 => (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))
    | 22 => (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))
    | 23 => (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000))
    | 24 => (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))
    | 25 => (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))
    | _ => (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-6409690685 / 1000000000000) (-6409690649 / 1000000000000)
      | 1 => orderedInterval (1956405422 / 1000000000000) (1956405519 / 1000000000000)
      | 2 => orderedInterval (-662922327 / 1000000000000) (-662922300 / 1000000000000)
      | 3 => orderedInterval (-1868860902 / 1000000000000) (-1868856232 / 1000000000000)
      | 4 => orderedInterval (-528603058 / 1000000000000) (-528602368 / 1000000000000)
      | 5 => orderedInterval (1527370158 / 1000000000000) (1527370204 / 1000000000000)
      | 6 => orderedInterval (-6734544368 / 1000000000000) (-6734533677 / 1000000000000)
      | 7 => orderedInterval (2569189700 / 1000000000000) (2569192470 / 1000000000000)
      | _ => orderedInterval (-5537364913 / 1000000000000) (-5537361484 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11357926272 / 1000000000000) (-11357926232 / 1000000000000)
      | 1 => orderedInterval (-3240989049 / 1000000000000) (-3240988961 / 1000000000000)
      | 2 => orderedInterval (524897335 / 1000000000000) (524897383 / 1000000000000)
      | 3 => orderedInterval (-8228768070 / 1000000000000) (-8228759255 / 1000000000000)
      | 4 => orderedInterval (3801708405 / 1000000000000) (3801709850 / 1000000000000)
      | 5 => orderedInterval (-898582182 / 1000000000000) (-898582115 / 1000000000000)
      | 6 => orderedInterval (4435864121 / 1000000000000) (4435875041 / 1000000000000)
      | 7 => orderedInterval (-1272645055 / 1000000000000) (-1272642083 / 1000000000000)
      | _ => orderedInterval (-4102909729 / 1000000000000) (-4102903414 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5696353916 / 1000000000000) (5696353962 / 1000000000000)
      | 1 => orderedInterval (-361421538 / 1000000000000) (-361421434 / 1000000000000)
      | 2 => orderedInterval (1964219570 / 1000000000000) (1964219654 / 1000000000000)
      | 3 => orderedInterval (2260862438 / 1000000000000) (2260880218 / 1000000000000)
      | 4 => orderedInterval (249312250 / 1000000000000) (249315300 / 1000000000000)
      | 5 => orderedInterval (-2287838486 / 1000000000000) (-2287838386 / 1000000000000)
      | 6 => orderedInterval (5956782665 / 1000000000000) (5956793848 / 1000000000000)
      | 7 => orderedInterval (-3012203952 / 1000000000000) (-3012200740 / 1000000000000)
      | _ => orderedInterval (12561904539 / 1000000000000) (12561916223 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10948931457 / 1000000000000) (10948931510 / 1000000000000)
      | 1 => orderedInterval (8004551013 / 1000000000000) (8004551157 / 1000000000000)
      | 2 => orderedInterval (-3723854626 / 1000000000000) (-3723854473 / 1000000000000)
      | 3 => orderedInterval (48086522828 / 1000000000000) (48086560406 / 1000000000000)
      | 4 => orderedInterval (-8170602323 / 1000000000000) (-8170595865 / 1000000000000)
      | 5 => orderedInterval (3939000503 / 1000000000000) (3939000656 / 1000000000000)
      | 6 => orderedInterval (-4621211025 / 1000000000000) (-4621199595 / 1000000000000)
      | 7 => orderedInterval (1950532958 / 1000000000000) (1950536429 / 1000000000000)
      | _ => orderedInterval (3078960124 / 1000000000000) (3078981761 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4629002562 / 1000000000000) (-4629002501 / 1000000000000)
      | 1 => orderedInterval (-384911525 / 1000000000000) (-384911311 / 1000000000000)
      | 2 => orderedInterval (-6340366658 / 1000000000000) (-6340366375 / 1000000000000)
      | 3 => orderedInterval (3176475913 / 1000000000000) (3176557979 / 1000000000000)
      | 4 => orderedInterval (3833696886 / 1000000000000) (3833710613 / 1000000000000)
      | 5 => orderedInterval (3109651586 / 1000000000000) (3109651829 / 1000000000000)
      | 6 => orderedInterval (-5783333683 / 1000000000000) (-5783321974 / 1000000000000)
      | 7 => orderedInterval (3254557580 / 1000000000000) (3254561340 / 1000000000000)
      | _ => orderedInterval (-32377717120 / 1000000000000) (-32377676953 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-15689020973 / 1000000000000) (-15688998517 / 1000000000000)
    | 1 => orderedInterval (-20339350496 / 1000000000000) (-20339319786 / 1000000000000)
    | 2 => orderedInterval (23027971402 / 1000000000000) (23028018645 / 1000000000000)
    | 3 => orderedInterval (59492830909 / 1000000000000) (59492911986 / 1000000000000)
    | _ => orderedInterval (-36140949583 / 1000000000000) (-36140797353 / 1000000000000)

theorem compactCertificate609_stateChecks0 :
    compactCertificate609.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (961 / 2)) (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1415736500932861 / 4000000000000)) (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (457820096259613 / 800000000000)) (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks1 :
    compactCertificate609.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413108380075127 / 4000000000000)) (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1109667217382219 / 4000000000000)) (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3012962356208223 / 4000000000000)) (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks2 :
    compactCertificate609.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2219334434765399 / 4000000000000)) (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 303 12 (3802867381314227 / 4000000000000)) (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2801174901107993 / 4000000000000)) (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks3 :
    compactCertificate609.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 342 12 (4297722652754039 / 4000000000000)) (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2481291330469631 / 4000000000000)) (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 351 12 (4403095008421579 / 4000000000000)) (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks4 :
    compactCertificate609.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 328 12 (4113942511329751 / 4000000000000)) (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2935903495234183 / 4000000000000)) (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (3329001652146657 / 4000000000000)) (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks5 :
    compactCertificate609.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2775374511690833 / 4000000000000)) (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2452127549743493 / 4000000000000)) (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (710722140177807 / 800000000000)) (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks6 :
    compactCertificate609.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1965894842988829 / 4000000000000)) (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1666510830090869 / 4000000000000)) (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1042825098892007 / 4000000000000)) (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks7 :
    compactCertificate609.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (560834806463769 / 4000000000000)) (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1522775597458307 / 4000000000000)) (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2079219892239139 / 4000000000000)) (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_stateChecks8 :
    compactCertificate609.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (879174901107993 / 4000000000000)) (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (3573797162672953 / 4000000000000)) (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2387130880382327 / 4000000000000)) (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_states : ∀ j,
    BesselStateValid (compactCertificate609.point j) (compactCertificate609.state j) :=
  compactCertificate609.statesValid_of_checks3 compactCertificate609_stateChecks0
    compactCertificate609_stateChecks1 compactCertificate609_stateChecks2
    compactCertificate609_stateChecks3 compactCertificate609_stateChecks4
    compactCertificate609_stateChecks5 compactCertificate609_stateChecks6
    compactCertificate609_stateChecks7 compactCertificate609_stateChecks8

theorem compactCertificate609_chunkChecks0_0 :
    compactCertificate609.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (961 / 2) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1415736500932861 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (457820096259613 / 800000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000)))) (orderedInterval (-6409690685 / 1000000000000) (-6409690649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (413108380075127 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1109667217382219 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3012962356208223 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000)))) (orderedInterval (1956405422 / 1000000000000) (1956405519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2219334434765399 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3802867381314227 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2801174901107993 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000)))) (orderedInterval (-662922327 / 1000000000000) (-662922300 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks0_1 :
    compactCertificate609.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4297722652754039 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2481291330469631 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4403095008421579 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000)))) (orderedInterval (-1868860902 / 1000000000000) (-1868856232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4113942511329751 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2935903495234183 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3329001652146657 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000)))) (orderedInterval (-528603058 / 1000000000000) (-528602368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2775374511690833 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2452127549743493 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (710722140177807 / 800000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000)))) (orderedInterval (1527370158 / 1000000000000) (1527370204 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks0_2 :
    compactCertificate609.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1965894842988829 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1666510830090869 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1042825098892007 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000)))) (orderedInterval (-6734544368 / 1000000000000) (-6734533677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (560834806463769 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1522775597458307 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2079219892239139 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000)))) (orderedInterval (2569189700 / 1000000000000) (2569192470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (879174901107993 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3573797162672953 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2387130880382327 / 4000000000000) 0 (IntervalRat.scale (961 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000)))) (orderedInterval (-5537364913 / 1000000000000) (-5537361484 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks0 :
    compactCertificate609.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate609.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate609_chunkChecks0_0
    compactCertificate609_chunkChecks0_1 compactCertificate609_chunkChecks0_2

theorem compactCertificate609_chunkChecks1_0 :
    compactCertificate609.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (961 / 2) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1415736500932861 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (457820096259613 / 800000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000)))) (orderedInterval (-11357926272 / 1000000000000) (-11357926232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (413108380075127 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1109667217382219 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3012962356208223 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000)))) (orderedInterval (-3240989049 / 1000000000000) (-3240988961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2219334434765399 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3802867381314227 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2801174901107993 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000)))) (orderedInterval (524897335 / 1000000000000) (524897383 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks1_1 :
    compactCertificate609.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4297722652754039 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2481291330469631 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4403095008421579 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000)))) (orderedInterval (-8228768070 / 1000000000000) (-8228759255 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4113942511329751 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2935903495234183 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3329001652146657 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000)))) (orderedInterval (3801708405 / 1000000000000) (3801709850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2775374511690833 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2452127549743493 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (710722140177807 / 800000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000)))) (orderedInterval (-898582182 / 1000000000000) (-898582115 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks1_2 :
    compactCertificate609.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1965894842988829 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1666510830090869 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1042825098892007 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000)))) (orderedInterval (4435864121 / 1000000000000) (4435875041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (560834806463769 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1522775597458307 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2079219892239139 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000)))) (orderedInterval (-1272645055 / 1000000000000) (-1272642083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (879174901107993 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3573797162672953 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2387130880382327 / 4000000000000) 1 (IntervalRat.scale (961 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000)))) (orderedInterval (-4102909729 / 1000000000000) (-4102903414 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks1 :
    compactCertificate609.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate609.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate609_chunkChecks1_0
    compactCertificate609_chunkChecks1_1 compactCertificate609_chunkChecks1_2

theorem compactCertificate609_chunkChecks2_0 :
    compactCertificate609.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (961 / 2) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1415736500932861 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (457820096259613 / 800000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000)))) (orderedInterval (5696353916 / 1000000000000) (5696353962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (413108380075127 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1109667217382219 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3012962356208223 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000)))) (orderedInterval (-361421538 / 1000000000000) (-361421434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2219334434765399 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3802867381314227 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2801174901107993 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000)))) (orderedInterval (1964219570 / 1000000000000) (1964219654 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks2_1 :
    compactCertificate609.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4297722652754039 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2481291330469631 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4403095008421579 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000)))) (orderedInterval (2260862438 / 1000000000000) (2260880218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4113942511329751 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2935903495234183 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3329001652146657 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000)))) (orderedInterval (249312250 / 1000000000000) (249315300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2775374511690833 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2452127549743493 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (710722140177807 / 800000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000)))) (orderedInterval (-2287838486 / 1000000000000) (-2287838386 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks2_2 :
    compactCertificate609.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1965894842988829 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1666510830090869 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1042825098892007 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000)))) (orderedInterval (5956782665 / 1000000000000) (5956793848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (560834806463769 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1522775597458307 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2079219892239139 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000)))) (orderedInterval (-3012203952 / 1000000000000) (-3012200740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (879174901107993 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3573797162672953 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2387130880382327 / 4000000000000) 2 (IntervalRat.scale (961 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000)))) (orderedInterval (12561904539 / 1000000000000) (12561916223 / 1000000000000))) = true
  rfl'

theorem compactCertificate609_chunkChecks2 :
    compactCertificate609.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate609.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate609_chunkChecks2_0
    compactCertificate609_chunkChecks2_1 compactCertificate609_chunkChecks2_2

theorem compactCertificate609_chunkChecks3_0 :
    compactCertificate609.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (961 / 2) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1415736500932861 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (457820096259613 / 800000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000)))) (orderedInterval (10948931457 / 1000000000000) (10948931510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (413108380075127 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1109667217382219 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3012962356208223 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000)))) (orderedInterval (8004551013 / 1000000000000) (8004551157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2219334434765399 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3802867381314227 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2801174901107993 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000)))) (orderedInterval (-3723854626 / 1000000000000) (-3723854473 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate609_chunkChecks3_1 :
    compactCertificate609.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4297722652754039 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2481291330469631 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4403095008421579 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000)))) (orderedInterval (48086522828 / 1000000000000) (48086560406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4113942511329751 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2935903495234183 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3329001652146657 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000)))) (orderedInterval (-8170602323 / 1000000000000) (-8170595865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2775374511690833 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2452127549743493 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (710722140177807 / 800000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000)))) (orderedInterval (3939000503 / 1000000000000) (3939000656 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate609_chunkChecks3_2 :
    compactCertificate609.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1965894842988829 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1666510830090869 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1042825098892007 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000)))) (orderedInterval (-4621211025 / 1000000000000) (-4621199595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (560834806463769 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1522775597458307 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2079219892239139 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000)))) (orderedInterval (1950532958 / 1000000000000) (1950536429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (879174901107993 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3573797162672953 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2387130880382327 / 4000000000000) 3 (IntervalRat.scale (961 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000)))) (orderedInterval (3078960124 / 1000000000000) (3078981761 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate609_chunkChecks3 :
    compactCertificate609.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate609.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate609_chunkChecks3_0
    compactCertificate609_chunkChecks3_1 compactCertificate609_chunkChecks3_2

theorem compactCertificate609_chunkChecks4_0 :
    compactCertificate609.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (961 / 2) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21192572788 / 1000000000000) (-21192572787 / 1000000000000), orderedInterval (-29571631968 / 1000000000000) (-29571631967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1415736500932861 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11753111089 / 1000000000000) (11753111156 / 1000000000000), orderedInterval (-40766591881 / 1000000000000) (-40766591813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (457820096259613 / 800000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32050963951 / 1000000000000) (32050963969 / 1000000000000), orderedInterval (9200860344 / 1000000000000) (9200860361 / 1000000000000)))) (orderedInterval (-4629002562 / 1000000000000) (-4629002501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (413108380075127 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29756730746 / 1000000000000) (-29756730745 / 1000000000000), orderedInterval (-72511152378 / 1000000000000) (-72511152377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1109667217382219 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47207104682 / 1000000000000) (47207105751 / 1000000000000), orderedInterval (-8227503623 / 1000000000000) (-8227502554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3012962356208223 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1266679569 / 1000000000000) (1266679570 / 1000000000000), orderedInterval (29043440092 / 1000000000000) (29043440093 / 1000000000000)))) (orderedInterval (-384911525 / 1000000000000) (-384911311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2219334434765399 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (14523502061 / 1000000000000) (14523502219 / 1000000000000), orderedInterval (-30614964482 / 1000000000000) (-30614964324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3802867381314227 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10088001288 / 1000000000000) (10088001292 / 1000000000000), orderedInterval (-23834973789 / 1000000000000) (-23834973785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2801174901107993 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14555097600 / 1000000000000) (-14555097599 / 1000000000000), orderedInterval (-26394619142 / 1000000000000) (-26394619141 / 1000000000000)))) (orderedInterval (-6340366658 / 1000000000000) (-6340366375 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate609_chunkChecks4_1 :
    compactCertificate609.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4297722652754039 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17312734196 / 1000000000000) (17312734197 / 1000000000000), orderedInterval (17102977173 / 1000000000000) (17102977174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2481291330469631 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25628790590 / 1000000000000) (-25628765759 / 1000000000000), orderedInterval (19241397472 / 1000000000000) (19241422304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4403095008421579 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21851261077 / 1000000000000) (21851279641 / 1000000000000), orderedInterval (-10052861190 / 1000000000000) (-10052842626 / 1000000000000)))) (orderedInterval (3176475913 / 1000000000000) (3176557979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4113942511329751 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22922191424 / 1000000000000) (-22922156481 / 1000000000000), orderedInterval (9683840040 / 1000000000000) (9683874984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2935903495234183 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10693263613 / 1000000000000) (-10693263598 / 1000000000000), orderedInterval (27448351528 / 1000000000000) (27448351543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3329001652146657 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13588761928 / 1000000000000) (-13588761927 / 1000000000000), orderedInterval (-24080908088 / 1000000000000) (-24080908087 / 1000000000000)))) (orderedInterval (3833696886 / 1000000000000) (3833710613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2775374511690833 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10012108536 / 1000000000000) (-10012108535 / 1000000000000), orderedInterval (-28580967263 / 1000000000000) (-28580967262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2452127549743493 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30110771885 / 1000000000000) (-30110771879 / 1000000000000), orderedInterval (-11456668331 / 1000000000000) (-11456668324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (710722140177807 / 800000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3130482220 / 1000000000000) (-3130482219 / 1000000000000), orderedInterval (-26583749285 / 1000000000000) (-26583749284 / 1000000000000)))) (orderedInterval (3109651586 / 1000000000000) (3109651829 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate609_chunkChecks4_2 :
    compactCertificate609.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1965894842988829 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29712378192 / 1000000000000) (29712444195 / 1000000000000), orderedInterval (-20340369778 / 1000000000000) (-20340303775 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1666510830090869 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15904277845 / 1000000000000) (15904278137 / 1000000000000), orderedInterval (-35727419465 / 1000000000000) (-35727419173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1042825098892007 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33283937478 / 1000000000000) (-33283937477 / 1000000000000), orderedInterval (-36461283704 / 1000000000000) (-36461283703 / 1000000000000)))) (orderedInterval (-5783333683 / 1000000000000) (-5783321974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (560834806463769 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24897456663 / 1000000000000) (24897457664 / 1000000000000), orderedInterval (-62703904758 / 1000000000000) (-62703903757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1522775597458307 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39866734290 / 1000000000000) (-39866734281 / 1000000000000), orderedInterval (-9052789326 / 1000000000000) (-9052789317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2079219892239139 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27720604344 / 1000000000000) (-27720569193 / 1000000000000), orderedInterval (21387756628 / 1000000000000) (21387791779 / 1000000000000)))) (orderedInterval (3254557580 / 1000000000000) (3254561340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (879174901107993 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33296768868 / 1000000000000) (33296768869 / 1000000000000), orderedInterval (42206271380 / 1000000000000) (42206271381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3573797162672953 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24019306680 / 1000000000000) (24019347166 / 1000000000000), orderedInterval (-11658779685 / 1000000000000) (-11658739199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2387130880382327 / 4000000000000) 4 (IntervalRat.scale (961 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20161707458 / 1000000000000) (20161707459 / 1000000000000), orderedInterval (25678606978 / 1000000000000) (25678606979 / 1000000000000)))) (orderedInterval (-32377717120 / 1000000000000) (-32377676953 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate609_chunkChecks4 :
    compactCertificate609.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate609.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate609_chunkChecks4_0
    compactCertificate609_chunkChecks4_1 compactCertificate609_chunkChecks4_2

theorem compactCertificate609_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate609.chunkCheck r b = true :=
  compactCertificate609.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate609_chunkChecks0
    · exact compactCertificate609_chunkChecks1
    · exact compactCertificate609_chunkChecks2
    · exact compactCertificate609_chunkChecks3
    · exact compactCertificate609_chunkChecks4)

theorem compactCertificate609_coefficient0 :
    compactCertificate609.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate609_coefficient1 :
    compactCertificate609.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate609_coefficient2 :
    compactCertificate609.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate609_coefficient3 :
    compactCertificate609.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate609_coefficient4 :
    compactCertificate609.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate609_coefficients : ∀ r : Fin 5,
    compactCertificate609.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate609_coefficient0
  · exact compactCertificate609_coefficient1
  · exact compactCertificate609_coefficient2
  · exact compactCertificate609_coefficient3
  · exact compactCertificate609_coefficient4

theorem compactCertificate609_lower : (1 : ℚ) ≤ compactCertificate609.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate609, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate609_proves {t : ℝ} (ht : t ∈ compactCertificate609.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate609.proves compactCertificate609_states compactCertificate609_chunks
    compactCertificate609_coefficients compactCertificate609_lower ht

end Erdos232
