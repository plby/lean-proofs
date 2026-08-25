/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate591 : CompactCertificate where
  left := 462
  right := 463
  center := 925 / 2
  grid := fun i =>
    match i.val with
    | 0 => 147
    | 1 => 108
    | 2 => 175
    | 3 => 32
    | 4 => 85
    | 5 => 231
    | 6 => 170
    | 7 => 291
    | 8 => 215
    | 9 => 329
    | 10 => 190
    | 11 => 337
    | 12 => 315
    | 13 => 225
    | 14 => 255
    | 15 => 213
    | 16 => 188
    | 17 => 272
    | 18 => 151
    | 19 => 128
    | 20 => 80
    | 21 => 43
    | 22 => 117
    | 23 => 159
    | 24 => 67
    | 25 => 274
    | _ => 183
  point := fun i =>
    match i.val with
    | 0 => 925 / 2
    | 1 => 54508065072337 / 160000000000
    | 2 => 17626788305521 / 32000000000
    | 3 => 15905317443059 / 160000000000
    | 4 => 42723919920023 / 160000000000
    | 5 => 116003753568891 / 160000000000
    | 6 => 85447839840083 / 160000000000
    | 7 => 146416329977759 / 160000000000
    | 8 => 107849605973981 / 160000000000
    | 9 => 165469030334963 / 160000000000
    | 10 => 95533589206427 / 160000000000
    | 11 => 169526030501143 / 160000000000
    | 12 => 158393208032467 / 160000000000
    | 13 => 113036867142211 / 160000000000
    | 14 => 128171759760069 / 160000000000
    | 15 => 106856250710261 / 160000000000
    | 16 => 94410738127481 / 160000000000
    | 17 => 27363911744619 / 32000000000
    | 18 => 75690019969393 / 160000000000
    | 19 => 64163268172073 / 160000000000
    | 20 => 40150394026019 / 160000000000
    | 21 => 21593015441373 / 160000000000
    | 22 => 58629237363119 / 160000000000
    | 23 => 80053211251663 / 160000000000
    | 24 => 33849605973981 / 160000000000
    | 25 => 137596769010301 / 160000000000
    | _ => 91908264905459 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))
    | 1 => (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))
    | 2 => (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000))
    | 3 => (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))
    | 4 => (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))
    | 5 => (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000))
    | 6 => (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))
    | 7 => (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))
    | 8 => (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000))
    | 9 => (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))
    | 10 => (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))
    | 11 => (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000))
    | 12 => (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))
    | 13 => (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))
    | 14 => (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000))
    | 15 => (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))
    | 16 => (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))
    | 17 => (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000))
    | 18 => (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))
    | 19 => (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))
    | 20 => (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000))
    | 21 => (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))
    | 22 => (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))
    | 23 => (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000))
    | 24 => (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))
    | 25 => (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))
    | _ => (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16220501055 / 1000000000000) (-16220499222 / 1000000000000)
      | 1 => orderedInterval (-745903521 / 1000000000000) (-745903456 / 1000000000000)
      | 2 => orderedInterval (1225981327 / 1000000000000) (1225981916 / 1000000000000)
      | 3 => orderedInterval (2840750064 / 1000000000000) (2840752932 / 1000000000000)
      | 4 => orderedInterval (-610747777 / 1000000000000) (-610747721 / 1000000000000)
      | 5 => orderedInterval (431865599 / 1000000000000) (431865660 / 1000000000000)
      | 6 => orderedInterval (-1638500035 / 1000000000000) (-1638499778 / 1000000000000)
      | 7 => orderedInterval (3179104195 / 1000000000000) (3179104316 / 1000000000000)
      | _ => orderedInterval (1600395868 / 1000000000000) (1600396013 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-974282525 / 1000000000000) (-974280777 / 1000000000000)
      | 1 => orderedInterval (2374261290 / 1000000000000) (2374261355 / 1000000000000)
      | 2 => orderedInterval (-1078068253 / 1000000000000) (-1078067100 / 1000000000000)
      | 3 => orderedInterval (3894851716 / 1000000000000) (3894858234 / 1000000000000)
      | 4 => orderedInterval (-3392177313 / 1000000000000) (-3392177221 / 1000000000000)
      | 5 => orderedInterval (-2553233518 / 1000000000000) (-2553233424 / 1000000000000)
      | 6 => orderedInterval (4133101259 / 1000000000000) (4133101509 / 1000000000000)
      | 7 => orderedInterval (895179734 / 1000000000000) (895179853 / 1000000000000)
      | _ => orderedInterval (3335429362 / 1000000000000) (3335429550 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17178887010 / 1000000000000) (17178888773 / 1000000000000)
      | 1 => orderedInterval (-123881805 / 1000000000000) (-123881717 / 1000000000000)
      | 2 => orderedInterval (-4049313394 / 1000000000000) (-4049311130 / 1000000000000)
      | 3 => orderedInterval (-6707060115 / 1000000000000) (-6707045258 / 1000000000000)
      | 4 => orderedInterval (431714430 / 1000000000000) (431714582 / 1000000000000)
      | 5 => orderedInterval (-2010417953 / 1000000000000) (-2010417804 / 1000000000000)
      | 6 => orderedInterval (2390221252 / 1000000000000) (2390221501 / 1000000000000)
      | 7 => orderedInterval (-3062231731 / 1000000000000) (-3062231607 / 1000000000000)
      | _ => orderedInterval (-3031619754 / 1000000000000) (-3031619484 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (591844874 / 1000000000000) (591846734 / 1000000000000)
      | 1 => orderedInterval (-7819994352 / 1000000000000) (-7819994221 / 1000000000000)
      | 2 => orderedInterval (2625448329 / 1000000000000) (2625452782 / 1000000000000)
      | 3 => orderedInterval (-13631430658 / 1000000000000) (-13631396769 / 1000000000000)
      | 4 => orderedInterval (6877276702 / 1000000000000) (6877276961 / 1000000000000)
      | 5 => orderedInterval (3959632275 / 1000000000000) (3959632518 / 1000000000000)
      | 6 => orderedInterval (-4259902477 / 1000000000000) (-4259902228 / 1000000000000)
      | 7 => orderedInterval (-340536127 / 1000000000000) (-340535996 / 1000000000000)
      | _ => orderedInterval (2801051020 / 1000000000000) (2801051432 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18402310896 / 1000000000000) (-18402308857 / 1000000000000)
      | 1 => orderedInterval (1175877265 / 1000000000000) (1175877467 / 1000000000000)
      | 2 => orderedInterval (14261614478 / 1000000000000) (14261623257 / 1000000000000)
      | 3 => orderedInterval (17948058262 / 1000000000000) (17948135679 / 1000000000000)
      | 4 => orderedInterval (3461945775 / 1000000000000) (3461946228 / 1000000000000)
      | 5 => orderedInterval (7644143088 / 1000000000000) (7644143497 / 1000000000000)
      | 6 => orderedInterval (-2788254224 / 1000000000000) (-2788253974 / 1000000000000)
      | 7 => orderedInterval (3621760755 / 1000000000000) (3621760894 / 1000000000000)
      | _ => orderedInterval (5200999687 / 1000000000000) (5201000346 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9937555335 / 1000000000000) (-9937549340 / 1000000000000)
    | 1 => orderedInterval (6635061752 / 1000000000000) (6635071979 / 1000000000000)
    | 2 => orderedInterval (1016297940 / 1000000000000) (1016317856 / 1000000000000)
    | 3 => orderedInterval (-9196610414 / 1000000000000) (-9196568787 / 1000000000000)
    | _ => orderedInterval (32123834190 / 1000000000000) (32123924537 / 1000000000000)

theorem compactCertificate591_stateChecks0 :
    compactCertificate591.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (925 / 2)) (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (54508065072337 / 160000000000)) (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (17626788305521 / 32000000000)) (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks1 :
    compactCertificate591.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (15905317443059 / 160000000000)) (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (42723919920023 / 160000000000)) (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (116003753568891 / 160000000000)) (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks2 :
    compactCertificate591.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (85447839840083 / 160000000000)) (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (146416329977759 / 160000000000)) (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (107849605973981 / 160000000000)) (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks3 :
    compactCertificate591.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 329 12 (165469030334963 / 160000000000)) (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (95533589206427 / 160000000000)) (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 337 12 (169526030501143 / 160000000000)) (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks4 :
    compactCertificate591.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 315 12 (158393208032467 / 160000000000)) (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (113036867142211 / 160000000000)) (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (128171759760069 / 160000000000)) (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks5 :
    compactCertificate591.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (106856250710261 / 160000000000)) (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (94410738127481 / 160000000000)) (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (27363911744619 / 32000000000)) (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks6 :
    compactCertificate591.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (75690019969393 / 160000000000)) (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (64163268172073 / 160000000000)) (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (40150394026019 / 160000000000)) (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks7 :
    compactCertificate591.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (21593015441373 / 160000000000)) (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (58629237363119 / 160000000000)) (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (80053211251663 / 160000000000)) (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_stateChecks8 :
    compactCertificate591.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33849605973981 / 160000000000)) (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (137596769010301 / 160000000000)) (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (91908264905459 / 160000000000)) (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_states : ∀ j,
    BesselStateValid (compactCertificate591.point j) (compactCertificate591.state j) :=
  compactCertificate591.statesValid_of_checks3 compactCertificate591_stateChecks0
    compactCertificate591_stateChecks1 compactCertificate591_stateChecks2
    compactCertificate591_stateChecks3 compactCertificate591_stateChecks4
    compactCertificate591_stateChecks5 compactCertificate591_stateChecks6
    compactCertificate591_stateChecks7 compactCertificate591_stateChecks8

theorem compactCertificate591_chunkChecks0_0 :
    compactCertificate591.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (925 / 2) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (54508065072337 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (17626788305521 / 32000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000)))) (orderedInterval (-16220501055 / 1000000000000) (-16220499222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (15905317443059 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (42723919920023 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (116003753568891 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000)))) (orderedInterval (-745903521 / 1000000000000) (-745903456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (85447839840083 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (146416329977759 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (107849605973981 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000)))) (orderedInterval (1225981327 / 1000000000000) (1225981916 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks0_1 :
    compactCertificate591.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (165469030334963 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (95533589206427 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (169526030501143 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000)))) (orderedInterval (2840750064 / 1000000000000) (2840752932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (158393208032467 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (113036867142211 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (128171759760069 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000)))) (orderedInterval (-610747777 / 1000000000000) (-610747721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (106856250710261 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (94410738127481 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (27363911744619 / 32000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000)))) (orderedInterval (431865599 / 1000000000000) (431865660 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks0_2 :
    compactCertificate591.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (75690019969393 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (64163268172073 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (40150394026019 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000)))) (orderedInterval (-1638500035 / 1000000000000) (-1638499778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (21593015441373 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (58629237363119 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (80053211251663 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000)))) (orderedInterval (3179104195 / 1000000000000) (3179104316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (33849605973981 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (137596769010301 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (91908264905459 / 160000000000) 0 (IntervalRat.scale (925 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000)))) (orderedInterval (1600395868 / 1000000000000) (1600396013 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks0 :
    compactCertificate591.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate591.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate591_chunkChecks0_0
    compactCertificate591_chunkChecks0_1 compactCertificate591_chunkChecks0_2

theorem compactCertificate591_chunkChecks1_0 :
    compactCertificate591.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (925 / 2) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (54508065072337 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (17626788305521 / 32000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000)))) (orderedInterval (-974282525 / 1000000000000) (-974280777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (15905317443059 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (42723919920023 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (116003753568891 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000)))) (orderedInterval (2374261290 / 1000000000000) (2374261355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (85447839840083 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (146416329977759 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (107849605973981 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000)))) (orderedInterval (-1078068253 / 1000000000000) (-1078067100 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks1_1 :
    compactCertificate591.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (165469030334963 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (95533589206427 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (169526030501143 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000)))) (orderedInterval (3894851716 / 1000000000000) (3894858234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (158393208032467 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (113036867142211 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (128171759760069 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000)))) (orderedInterval (-3392177313 / 1000000000000) (-3392177221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (106856250710261 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (94410738127481 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (27363911744619 / 32000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000)))) (orderedInterval (-2553233518 / 1000000000000) (-2553233424 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks1_2 :
    compactCertificate591.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (75690019969393 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (64163268172073 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (40150394026019 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000)))) (orderedInterval (4133101259 / 1000000000000) (4133101509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (21593015441373 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (58629237363119 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (80053211251663 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000)))) (orderedInterval (895179734 / 1000000000000) (895179853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (33849605973981 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (137596769010301 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (91908264905459 / 160000000000) 1 (IntervalRat.scale (925 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000)))) (orderedInterval (3335429362 / 1000000000000) (3335429550 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks1 :
    compactCertificate591.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate591.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate591_chunkChecks1_0
    compactCertificate591_chunkChecks1_1 compactCertificate591_chunkChecks1_2

theorem compactCertificate591_chunkChecks2_0 :
    compactCertificate591.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (925 / 2) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (54508065072337 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (17626788305521 / 32000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000)))) (orderedInterval (17178887010 / 1000000000000) (17178888773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (15905317443059 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (42723919920023 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (116003753568891 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000)))) (orderedInterval (-123881805 / 1000000000000) (-123881717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (85447839840083 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (146416329977759 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (107849605973981 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000)))) (orderedInterval (-4049313394 / 1000000000000) (-4049311130 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks2_1 :
    compactCertificate591.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (165469030334963 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (95533589206427 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (169526030501143 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000)))) (orderedInterval (-6707060115 / 1000000000000) (-6707045258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (158393208032467 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (113036867142211 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (128171759760069 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000)))) (orderedInterval (431714430 / 1000000000000) (431714582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (106856250710261 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (94410738127481 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (27363911744619 / 32000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000)))) (orderedInterval (-2010417953 / 1000000000000) (-2010417804 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks2_2 :
    compactCertificate591.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (75690019969393 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (64163268172073 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (40150394026019 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000)))) (orderedInterval (2390221252 / 1000000000000) (2390221501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (21593015441373 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (58629237363119 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (80053211251663 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000)))) (orderedInterval (-3062231731 / 1000000000000) (-3062231607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (33849605973981 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (137596769010301 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (91908264905459 / 160000000000) 2 (IntervalRat.scale (925 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000)))) (orderedInterval (-3031619754 / 1000000000000) (-3031619484 / 1000000000000))) = true
  rfl'

theorem compactCertificate591_chunkChecks2 :
    compactCertificate591.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate591.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate591_chunkChecks2_0
    compactCertificate591_chunkChecks2_1 compactCertificate591_chunkChecks2_2

theorem compactCertificate591_chunkChecks3_0 :
    compactCertificate591.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (925 / 2) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (54508065072337 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (17626788305521 / 32000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000)))) (orderedInterval (591844874 / 1000000000000) (591846734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (15905317443059 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (42723919920023 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (116003753568891 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000)))) (orderedInterval (-7819994352 / 1000000000000) (-7819994221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (85447839840083 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (146416329977759 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (107849605973981 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000)))) (orderedInterval (2625448329 / 1000000000000) (2625452782 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate591_chunkChecks3_1 :
    compactCertificate591.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (165469030334963 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (95533589206427 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (169526030501143 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000)))) (orderedInterval (-13631430658 / 1000000000000) (-13631396769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (158393208032467 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (113036867142211 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (128171759760069 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000)))) (orderedInterval (6877276702 / 1000000000000) (6877276961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (106856250710261 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (94410738127481 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (27363911744619 / 32000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000)))) (orderedInterval (3959632275 / 1000000000000) (3959632518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate591_chunkChecks3_2 :
    compactCertificate591.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (75690019969393 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (64163268172073 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (40150394026019 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000)))) (orderedInterval (-4259902477 / 1000000000000) (-4259902228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (21593015441373 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (58629237363119 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (80053211251663 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000)))) (orderedInterval (-340536127 / 1000000000000) (-340535996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (33849605973981 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (137596769010301 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (91908264905459 / 160000000000) 3 (IntervalRat.scale (925 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000)))) (orderedInterval (2801051020 / 1000000000000) (2801051432 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate591_chunkChecks3 :
    compactCertificate591.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate591.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate591_chunkChecks3_0
    compactCertificate591_chunkChecks3_1 compactCertificate591_chunkChecks3_2

theorem compactCertificate591_chunkChecks4_0 :
    compactCertificate591.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (925 / 2) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36916300395 / 1000000000000) (-36916300285 / 1000000000000), orderedInterval (-3656191806 / 1000000000000) (-3656191696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (54508065072337 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35735534671 / 1000000000000) (35735634838 / 1000000000000), orderedInterval (-24376683658 / 1000000000000) (-24376583491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (17626788305521 / 32000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32738930217 / 1000000000000) (-32738916187 / 1000000000000), orderedInterval (9189070886 / 1000000000000) (9189084916 / 1000000000000)))) (orderedInterval (-18402310896 / 1000000000000) (-18402308857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (15905317443059 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-26580938290 / 1000000000000) (-26580937498 / 1000000000000), orderedInterval (75616218785 / 1000000000000) (75616219576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (42723919920023 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34132342839 / 1000000000000) (-34132342838 / 1000000000000), orderedInterval (-34851818115 / 1000000000000) (-34851818114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (116003753568891 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2981357202 / 1000000000000) (-2981357201 / 1000000000000), orderedInterval (-29479794965 / 1000000000000) (-29479794964 / 1000000000000)))) (orderedInterval (1175877265 / 1000000000000) (1175877467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (85447839840083 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23871123670 / 1000000000000) (23871123671 / 1000000000000), orderedInterval (24922228483 / 1000000000000) (24922228484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (146416329977759 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26207374068 / 1000000000000) (-26207356230 / 1000000000000), orderedInterval (2990148850 / 1000000000000) (2990166687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (107849605973981 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (17280749408 / 1000000000000) (17280749943 / 1000000000000), orderedInterval (-25426031349 / 1000000000000) (-25426030814 / 1000000000000)))) (orderedInterval (14261614478 / 1000000000000) (14261623257 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate591_chunkChecks4_1 :
    compactCertificate591.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (165469030334963 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24373394831 / 1000000000000) (-24373393405 / 1000000000000), orderedInterval (-4626751864 / 1000000000000) (-4626750437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (95533589206427 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26889008619 / 1000000000000) (26889008620 / 1000000000000), orderedInterval (18502983772 / 1000000000000) (18502983773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (169526030501143 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24496781587 / 1000000000000) (-24496764480 / 1000000000000), orderedInterval (880331880 / 1000000000000) (880348988 / 1000000000000)))) (orderedInterval (17948058262 / 1000000000000) (17948135679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (158393208032467 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23054034305 / 1000000000000) (-23054034260 / 1000000000000), orderedInterval (-10551939704 / 1000000000000) (-10551939660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (113036867142211 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11891133564 / 1000000000000) (-11891133563 / 1000000000000), orderedInterval (-27554523659 / 1000000000000) (-27554523658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (128171759760069 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19269635968 / 1000000000000) (-19269635967 / 1000000000000), orderedInterval (-20564402282 / 1000000000000) (-20564402281 / 1000000000000)))) (orderedInterval (3461945775 / 1000000000000) (3461946228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (106856250710261 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15406721689 / 1000000000000) (15406721902 / 1000000000000), orderedInterval (-26767253331 / 1000000000000) (-26767253118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (94410738127481 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7580366298 / 1000000000000) (7580366299 / 1000000000000), orderedInterval (31953430114 / 1000000000000) (31953430115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (27363911744619 / 32000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26861209190 / 1000000000000) (26861209741 / 1000000000000), orderedInterval (4775263819 / 1000000000000) (4775264370 / 1000000000000)))) (orderedInterval (7644143088 / 1000000000000) (7644143497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate591_chunkChecks4_2 :
    compactCertificate591.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (75690019969393 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18631553923 / 1000000000000) (18631554771 / 1000000000000), orderedInterval (-31620429442 / 1000000000000) (-31620428594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (64163268172073 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-12470878528 / 1000000000000) (-12470878446 / 1000000000000), orderedInterval (37857031366 / 1000000000000) (37857031448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (40150394026019 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (19495879565 / 1000000000000) (19495879566 / 1000000000000), orderedInterval (46403105082 / 1000000000000) (46403105083 / 1000000000000)))) (orderedInterval (-2788254224 / 1000000000000) (-2788253974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (21593015441373 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41692837007 / 1000000000000) (-41692837006 / 1000000000000), orderedInterval (-54425230414 / 1000000000000) (-54425230413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (58629237363119 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14235682432 / 1000000000000) (14235682591 / 1000000000000), orderedInterval (-39194553968 / 1000000000000) (-39194553809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (80053211251663 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35650370855 / 1000000000000) (-35650370056 / 1000000000000), orderedInterval (1237156895 / 1000000000000) (1237157694 / 1000000000000)))) (orderedInterval (3621760755 / 1000000000000) (3621760894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (33849605973981 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52606776645 / 1000000000000) (-52606773881 / 1000000000000), orderedInterval (15670662621 / 1000000000000) (15670665385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (137596769010301 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-852230248 / 1000000000000) (-852230247 / 1000000000000), orderedInterval (27195104520 / 1000000000000) (27195104521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (91908264905459 / 160000000000) 4 (IntervalRat.scale (925 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9850173160 / 1000000000000) (-9850173159 / 1000000000000), orderedInterval (-31791494255 / 1000000000000) (-31791494254 / 1000000000000)))) (orderedInterval (5200999687 / 1000000000000) (5201000346 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate591_chunkChecks4 :
    compactCertificate591.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate591.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate591_chunkChecks4_0
    compactCertificate591_chunkChecks4_1 compactCertificate591_chunkChecks4_2

theorem compactCertificate591_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate591.chunkCheck r b = true :=
  compactCertificate591.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate591_chunkChecks0
    · exact compactCertificate591_chunkChecks1
    · exact compactCertificate591_chunkChecks2
    · exact compactCertificate591_chunkChecks3
    · exact compactCertificate591_chunkChecks4)

theorem compactCertificate591_coefficient0 :
    compactCertificate591.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate591_coefficient1 :
    compactCertificate591.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate591_coefficient2 :
    compactCertificate591.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate591_coefficient3 :
    compactCertificate591.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate591_coefficient4 :
    compactCertificate591.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate591_coefficients : ∀ r : Fin 5,
    compactCertificate591.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate591_coefficient0
  · exact compactCertificate591_coefficient1
  · exact compactCertificate591_coefficient2
  · exact compactCertificate591_coefficient3
  · exact compactCertificate591_coefficient4

theorem compactCertificate591_lower : (1 : ℚ) ≤ compactCertificate591.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate591, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate591_proves {t : ℝ} (ht : t ∈ compactCertificate591.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate591.proves compactCertificate591_states compactCertificate591_chunks
    compactCertificate591_coefficients compactCertificate591_lower ht

end Erdos232
