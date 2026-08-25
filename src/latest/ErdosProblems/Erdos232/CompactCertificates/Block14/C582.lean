/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate582 : CompactCertificate where
  left := 453
  right := 454
  center := 907 / 2
  grid := fun i =>
    match i.val with
    | 0 => 144
    | 1 => 106
    | 2 => 172
    | 3 => 31
    | 4 => 83
    | 5 => 226
    | 6 => 167
    | 7 => 286
    | 8 => 210
    | 9 => 323
    | 10 => 186
    | 11 => 331
    | 12 => 309
    | 13 => 221
    | 14 => 250
    | 15 => 209
    | 16 => 184
    | 17 => 267
    | 18 => 148
    | 19 => 125
    | 20 => 78
    | 21 => 42
    | 22 => 114
    | 23 => 156
    | 24 => 66
    | 25 => 269
    | _ => 179
  point := fun i =>
    match i.val with
    | 0 => 907 / 2
    | 1 => 1336184189746207 / 4000000000000
    | 2 => 432094513327231 / 800000000000
    | 3 => 389895214077149 / 4000000000000
    | 4 => 1047313388309753 / 4000000000000
    | 5 => 2843659580729301 / 4000000000000
    | 6 => 2094626776620413 / 4000000000000
    | 7 => 3589178683508849 / 4000000000000
    | 8 => 2643772773470291 / 4000000000000
    | 9 => 4056227311184093 / 4000000000000
    | 10 => 2341863930006197 / 4000000000000
    | 11 => 4155678639582073 / 4000000000000
    | 12 => 3882774045552637 / 4000000000000
    | 13 => 2770930770215821 / 4000000000000
    | 14 => 3141940164929259 / 4000000000000
    | 15 => 2619422145789371 / 4000000000000
    | 16 => 2314338904908791 / 4000000000000
    | 17 => 670785620334309 / 800000000000
    | 18 => 1855428327357823 / 4000000000000
    | 19 => 1572867141407303 / 4000000000000
    | 20 => 984227226529709 / 4000000000000
    | 21 => 529320675819603 / 4000000000000
    | 22 => 1437208602387809 / 4000000000000
    | 23 => 1962385475817793 / 4000000000000
    | 24 => 829772773470291 / 4000000000000
    | 25 => 3372980256549811 / 4000000000000
    | _ => 2252994493763549 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))
    | 1 => (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))
    | 2 => (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000))
    | 3 => (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))
    | 4 => (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))
    | 5 => (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000))
    | 6 => (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))
    | 7 => (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))
    | 8 => (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000))
    | 9 => (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))
    | 10 => (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))
    | 11 => (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000))
    | 12 => (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))
    | 13 => (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))
    | 14 => (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000))
    | 15 => (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))
    | 16 => (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))
    | 17 => (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000))
    | 18 => (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))
    | 19 => (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))
    | 20 => (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000))
    | 21 => (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))
    | 22 => (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))
    | 23 => (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000))
    | 24 => (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))
    | 25 => (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))
    | _ => (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15519267245 / 1000000000000) (15519273029 / 1000000000000)
      | 1 => orderedInterval (-3165287756 / 1000000000000) (-3165287027 / 1000000000000)
      | 2 => orderedInterval (1015584411 / 1000000000000) (1015586623 / 1000000000000)
      | 3 => orderedInterval (3346787125 / 1000000000000) (3346789703 / 1000000000000)
      | 4 => orderedInterval (2200786372 / 1000000000000) (2200786778 / 1000000000000)
      | 5 => orderedInterval (-1858563292 / 1000000000000) (-1858562940 / 1000000000000)
      | 6 => orderedInterval (5636422160 / 1000000000000) (5636422337 / 1000000000000)
      | 7 => orderedInterval (-4721708727 / 1000000000000) (-4721708338 / 1000000000000)
      | _ => orderedInterval (4573007849 / 1000000000000) (4573010926 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2787050835 / 1000000000000) (-2787045056 / 1000000000000)
      | 1 => orderedInterval (853000422 / 1000000000000) (853001405 / 1000000000000)
      | 2 => orderedInterval (-1937208483 / 1000000000000) (-1937205253 / 1000000000000)
      | 3 => orderedInterval (874032171 / 1000000000000) (874035641 / 1000000000000)
      | 4 => orderedInterval (-2554553581 / 1000000000000) (-2554552956 / 1000000000000)
      | 5 => orderedInterval (-2075526732 / 1000000000000) (-2075526224 / 1000000000000)
      | 6 => orderedInterval (-5448651245 / 1000000000000) (-5448651102 / 1000000000000)
      | 7 => orderedInterval (-683234265 / 1000000000000) (-683233950 / 1000000000000)
      | _ => orderedInterval (1210266184 / 1000000000000) (1210271497 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15773120573 / 1000000000000) (-15773114782 / 1000000000000)
      | 1 => orderedInterval (5726311668 / 1000000000000) (5726313120 / 1000000000000)
      | 2 => orderedInterval (-2746881068 / 1000000000000) (-2746876340 / 1000000000000)
      | 3 => orderedInterval (-9210443421 / 1000000000000) (-9210438616 / 1000000000000)
      | 4 => orderedInterval (-5746541183 / 1000000000000) (-5746540215 / 1000000000000)
      | 5 => orderedInterval (3458808446 / 1000000000000) (3458809183 / 1000000000000)
      | 6 => orderedInterval (-4025193073 / 1000000000000) (-4025192948 / 1000000000000)
      | 7 => orderedInterval (3766707567 / 1000000000000) (3766707827 / 1000000000000)
      | _ => orderedInterval (-2980669377 / 1000000000000) (-2980659990 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1931642106 / 1000000000000) (1931647898 / 1000000000000)
      | 1 => orderedInterval (-1181083327 / 1000000000000) (-1181081101 / 1000000000000)
      | 2 => orderedInterval (6784720784 / 1000000000000) (6784727704 / 1000000000000)
      | 3 => orderedInterval (-5930867311 / 1000000000000) (-5930860388 / 1000000000000)
      | 4 => orderedInterval (4418153023 / 1000000000000) (4418154524 / 1000000000000)
      | 5 => orderedInterval (5599161910 / 1000000000000) (5599162982 / 1000000000000)
      | 6 => orderedInterval (5709301554 / 1000000000000) (5709301669 / 1000000000000)
      | 7 => orderedInterval (784444670 / 1000000000000) (784444888 / 1000000000000)
      | _ => orderedInterval (-5641834004 / 1000000000000) (-5641817176 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16297317047 / 1000000000000) (16297322856 / 1000000000000)
      | 1 => orderedInterval (-12924547489 / 1000000000000) (-12924544026 / 1000000000000)
      | 2 => orderedInterval (8138994957 / 1000000000000) (8139005114 / 1000000000000)
      | 3 => orderedInterval (34031521904 / 1000000000000) (34031532484 / 1000000000000)
      | 4 => orderedInterval (16345353884 / 1000000000000) (16345356232 / 1000000000000)
      | 5 => orderedInterval (-7292663802 / 1000000000000) (-7292662232 / 1000000000000)
      | 6 => orderedInterval (3355352737 / 1000000000000) (3355352846 / 1000000000000)
      | 7 => orderedInterval (-3998313032 / 1000000000000) (-3998312846 / 1000000000000)
      | _ => orderedInterval (-8357167864 / 1000000000000) (-8357137314 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (22546295387 / 1000000000000) (22546311091 / 1000000000000)
    | 1 => orderedInterval (-12548926364 / 1000000000000) (-12548905998 / 1000000000000)
    | 2 => orderedInterval (-27531021014 / 1000000000000) (-27530992761 / 1000000000000)
    | 3 => orderedInterval (12473639405 / 1000000000000) (12473681000 / 1000000000000)
    | _ => orderedInterval (45595848342 / 1000000000000) (45595913114 / 1000000000000)

theorem compactCertificate582_stateChecks0 :
    compactCertificate582.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (907 / 2)) (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1336184189746207 / 4000000000000)) (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (432094513327231 / 800000000000)) (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks1 :
    compactCertificate582.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (389895214077149 / 4000000000000)) (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1047313388309753 / 4000000000000)) (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2843659580729301 / 4000000000000)) (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks2 :
    compactCertificate582.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2094626776620413 / 4000000000000)) (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (3589178683508849 / 4000000000000)) (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2643772773470291 / 4000000000000)) (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks3 :
    compactCertificate582.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 323 12 (4056227311184093 / 4000000000000)) (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2341863930006197 / 4000000000000)) (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 331 12 (4155678639582073 / 4000000000000)) (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks4 :
    compactCertificate582.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 309 12 (3882774045552637 / 4000000000000)) (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2770930770215821 / 4000000000000)) (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (3141940164929259 / 4000000000000)) (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks5 :
    compactCertificate582.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2619422145789371 / 4000000000000)) (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2314338904908791 / 4000000000000)) (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (670785620334309 / 800000000000)) (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks6 :
    compactCertificate582.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1855428327357823 / 4000000000000)) (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1572867141407303 / 4000000000000)) (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (984227226529709 / 4000000000000)) (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks7 :
    compactCertificate582.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (529320675819603 / 4000000000000)) (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1437208602387809 / 4000000000000)) (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1962385475817793 / 4000000000000)) (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_stateChecks8 :
    compactCertificate582.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (829772773470291 / 4000000000000)) (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (3372980256549811 / 4000000000000)) (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2252994493763549 / 4000000000000)) (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_states : ∀ j,
    BesselStateValid (compactCertificate582.point j) (compactCertificate582.state j) :=
  compactCertificate582.statesValid_of_checks3 compactCertificate582_stateChecks0
    compactCertificate582_stateChecks1 compactCertificate582_stateChecks2
    compactCertificate582_stateChecks3 compactCertificate582_stateChecks4
    compactCertificate582_stateChecks5 compactCertificate582_stateChecks6
    compactCertificate582_stateChecks7 compactCertificate582_stateChecks8

theorem compactCertificate582_chunkChecks0_0 :
    compactCertificate582.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (907 / 2) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1336184189746207 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (432094513327231 / 800000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000)))) (orderedInterval (15519267245 / 1000000000000) (15519273029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (389895214077149 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1047313388309753 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2843659580729301 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000)))) (orderedInterval (-3165287756 / 1000000000000) (-3165287027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2094626776620413 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3589178683508849 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2643772773470291 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000)))) (orderedInterval (1015584411 / 1000000000000) (1015586623 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks0_1 :
    compactCertificate582.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4056227311184093 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2341863930006197 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4155678639582073 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000)))) (orderedInterval (3346787125 / 1000000000000) (3346789703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3882774045552637 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2770930770215821 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3141940164929259 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000)))) (orderedInterval (2200786372 / 1000000000000) (2200786778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2619422145789371 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2314338904908791 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (670785620334309 / 800000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000)))) (orderedInterval (-1858563292 / 1000000000000) (-1858562940 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks0_2 :
    compactCertificate582.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1855428327357823 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1572867141407303 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (984227226529709 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000)))) (orderedInterval (5636422160 / 1000000000000) (5636422337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (529320675819603 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1437208602387809 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1962385475817793 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000)))) (orderedInterval (-4721708727 / 1000000000000) (-4721708338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (829772773470291 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3372980256549811 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2252994493763549 / 4000000000000) 0 (IntervalRat.scale (907 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000)))) (orderedInterval (4573007849 / 1000000000000) (4573010926 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks0 :
    compactCertificate582.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate582.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate582_chunkChecks0_0
    compactCertificate582_chunkChecks0_1 compactCertificate582_chunkChecks0_2

theorem compactCertificate582_chunkChecks1_0 :
    compactCertificate582.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (907 / 2) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1336184189746207 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (432094513327231 / 800000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000)))) (orderedInterval (-2787050835 / 1000000000000) (-2787045056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (389895214077149 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1047313388309753 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2843659580729301 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000)))) (orderedInterval (853000422 / 1000000000000) (853001405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2094626776620413 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3589178683508849 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2643772773470291 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000)))) (orderedInterval (-1937208483 / 1000000000000) (-1937205253 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks1_1 :
    compactCertificate582.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4056227311184093 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2341863930006197 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4155678639582073 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000)))) (orderedInterval (874032171 / 1000000000000) (874035641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3882774045552637 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2770930770215821 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3141940164929259 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000)))) (orderedInterval (-2554553581 / 1000000000000) (-2554552956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2619422145789371 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2314338904908791 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (670785620334309 / 800000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000)))) (orderedInterval (-2075526732 / 1000000000000) (-2075526224 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks1_2 :
    compactCertificate582.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1855428327357823 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1572867141407303 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (984227226529709 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000)))) (orderedInterval (-5448651245 / 1000000000000) (-5448651102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (529320675819603 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1437208602387809 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1962385475817793 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000)))) (orderedInterval (-683234265 / 1000000000000) (-683233950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (829772773470291 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3372980256549811 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2252994493763549 / 4000000000000) 1 (IntervalRat.scale (907 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000)))) (orderedInterval (1210266184 / 1000000000000) (1210271497 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks1 :
    compactCertificate582.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate582.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate582_chunkChecks1_0
    compactCertificate582_chunkChecks1_1 compactCertificate582_chunkChecks1_2

theorem compactCertificate582_chunkChecks2_0 :
    compactCertificate582.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (907 / 2) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1336184189746207 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (432094513327231 / 800000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000)))) (orderedInterval (-15773120573 / 1000000000000) (-15773114782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (389895214077149 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1047313388309753 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2843659580729301 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000)))) (orderedInterval (5726311668 / 1000000000000) (5726313120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2094626776620413 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3589178683508849 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2643772773470291 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000)))) (orderedInterval (-2746881068 / 1000000000000) (-2746876340 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks2_1 :
    compactCertificate582.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4056227311184093 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2341863930006197 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4155678639582073 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000)))) (orderedInterval (-9210443421 / 1000000000000) (-9210438616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3882774045552637 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2770930770215821 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3141940164929259 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000)))) (orderedInterval (-5746541183 / 1000000000000) (-5746540215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2619422145789371 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2314338904908791 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (670785620334309 / 800000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000)))) (orderedInterval (3458808446 / 1000000000000) (3458809183 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks2_2 :
    compactCertificate582.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1855428327357823 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1572867141407303 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (984227226529709 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000)))) (orderedInterval (-4025193073 / 1000000000000) (-4025192948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (529320675819603 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1437208602387809 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1962385475817793 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000)))) (orderedInterval (3766707567 / 1000000000000) (3766707827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (829772773470291 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3372980256549811 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2252994493763549 / 4000000000000) 2 (IntervalRat.scale (907 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000)))) (orderedInterval (-2980669377 / 1000000000000) (-2980659990 / 1000000000000))) = true
  rfl'

theorem compactCertificate582_chunkChecks2 :
    compactCertificate582.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate582.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate582_chunkChecks2_0
    compactCertificate582_chunkChecks2_1 compactCertificate582_chunkChecks2_2

theorem compactCertificate582_chunkChecks3_0 :
    compactCertificate582.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (907 / 2) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1336184189746207 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (432094513327231 / 800000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000)))) (orderedInterval (1931642106 / 1000000000000) (1931647898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (389895214077149 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1047313388309753 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2843659580729301 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000)))) (orderedInterval (-1181083327 / 1000000000000) (-1181081101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2094626776620413 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3589178683508849 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2643772773470291 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000)))) (orderedInterval (6784720784 / 1000000000000) (6784727704 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate582_chunkChecks3_1 :
    compactCertificate582.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4056227311184093 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2341863930006197 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4155678639582073 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000)))) (orderedInterval (-5930867311 / 1000000000000) (-5930860388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3882774045552637 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2770930770215821 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3141940164929259 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000)))) (orderedInterval (4418153023 / 1000000000000) (4418154524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2619422145789371 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2314338904908791 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (670785620334309 / 800000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000)))) (orderedInterval (5599161910 / 1000000000000) (5599162982 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate582_chunkChecks3_2 :
    compactCertificate582.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1855428327357823 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1572867141407303 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (984227226529709 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000)))) (orderedInterval (5709301554 / 1000000000000) (5709301669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (529320675819603 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1437208602387809 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1962385475817793 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000)))) (orderedInterval (784444670 / 1000000000000) (784444888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (829772773470291 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3372980256549811 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2252994493763549 / 4000000000000) 3 (IntervalRat.scale (907 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000)))) (orderedInterval (-5641834004 / 1000000000000) (-5641817176 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate582_chunkChecks3 :
    compactCertificate582.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate582.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate582_chunkChecks3_0
    compactCertificate582_chunkChecks3_1 compactCertificate582_chunkChecks3_2

theorem compactCertificate582_chunkChecks4_0 :
    compactCertificate582.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (907 / 2) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35506005947 / 1000000000000) (35506020373 / 1000000000000), orderedInterval (-12002203282 / 1000000000000) (-12002188856 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1336184189746207 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42282382272 / 1000000000000) (42282385942 / 1000000000000), orderedInterval (-10925269336 / 1000000000000) (-10925265666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (432094513327231 / 800000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17926367605 / 1000000000000) (17926367606 / 1000000000000), orderedInterval (29263316505 / 1000000000000) (29263316506 / 1000000000000)))) (orderedInterval (16297317047 / 1000000000000) (16297322856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (389895214077149 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61693645236 / 1000000000000) (-61693645235 / 1000000000000), orderedInterval (-51885732283 / 1000000000000) (-51885732282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1047313388309753 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47246640478 / 1000000000000) (-47246636716 / 1000000000000), orderedInterval (14203722050 / 1000000000000) (14203725811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2843659580729301 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29674677427 / 1000000000000) (29674684977 / 1000000000000), orderedInterval (-3881797025 / 1000000000000) (-3881789474 / 1000000000000)))) (orderedInterval (-12924547489 / 1000000000000) (-12924544026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2094626776620413 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7067750481 / 1000000000000) (7067750487 / 1000000000000), orderedInterval (-34150080703 / 1000000000000) (-34150080697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3589178683508849 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10753325465 / 1000000000000) (-10753325457 / 1000000000000), orderedInterval (24375112563 / 1000000000000) (24375112571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2643772773470291 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28298083380 / 1000000000000) (28298173791 / 1000000000000), orderedInterval (-12765650223 / 1000000000000) (-12765559813 / 1000000000000)))) (orderedInterval (8138994957 / 1000000000000) (8139005114 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate582_chunkChecks4_1 :
    compactCertificate582.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4056227311184093 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2692691446 / 1000000000000) (-2692691445 / 1000000000000), orderedInterval (-24909402014 / 1000000000000) (-24909402013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2341863930006197 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31041866679 / 1000000000000) (31041899057 / 1000000000000), orderedInterval (-11151900582 / 1000000000000) (-11151868204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4155678639582073 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3998297719 / 1000000000000) (3998297720 / 1000000000000), orderedInterval (-24431099818 / 1000000000000) (-24431099817 / 1000000000000)))) (orderedInterval (34031521904 / 1000000000000) (34031532484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3882774045552637 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17014104556 / 1000000000000) (-17014104555 / 1000000000000), orderedInterval (-19131779481 / 1000000000000) (-19131779480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2770930770215821 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21191637103 / 1000000000000) (21191640823 / 1000000000000), orderedInterval (-21692755204 / 1000000000000) (-21692751485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3141940164929259 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21798434206 / 1000000000000) (21798434207 / 1000000000000), orderedInterval (18297542922 / 1000000000000) (18297542923 / 1000000000000)))) (orderedInterval (16345353884 / 1000000000000) (16345356232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2619422145789371 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25400172228 / 1000000000000) (25400198799 / 1000000000000), orderedInterval (-18102090858 / 1000000000000) (-18102064288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2314338904908791 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32107088966 / 1000000000000) (32107088993 / 1000000000000), orderedInterval (8305300040 / 1000000000000) (8305300067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (670785620334309 / 800000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12283029224 / 1000000000000) (-12283029223 / 1000000000000), orderedInterval (-24658035989 / 1000000000000) (-24658035988 / 1000000000000)))) (orderedInterval (-7292663802 / 1000000000000) (-7292662232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate582_chunkChecks4_2 :
    compactCertificate582.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1855428327357823 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11424862552 / 1000000000000) (-11424862504 / 1000000000000), orderedInterval (35253218331 / 1000000000000) (35253218379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1572867141407303 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38800350133 / 1000000000000) (-38800350128 / 1000000000000), orderedInterval (-10606003156 / 1000000000000) (-10606003150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (984227226529709 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49564168628 / 1000000000000) (49564170330 / 1000000000000), orderedInterval (-11532081749 / 1000000000000) (-11532080048 / 1000000000000)))) (orderedInterval (3355352737 / 1000000000000) (3355352846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (529320675819603 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (63801697359 / 1000000000000) (63801697361 / 1000000000000), orderedInterval (26964878237 / 1000000000000) (26964878238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1437208602387809 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39170290492 / 1000000000000) (39170305222 / 1000000000000), orderedInterval (-15465855082 / 1000000000000) (-15465840352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1962385475817793 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34642363379 / 1000000000000) (34642363388 / 1000000000000), orderedInterval (9841473243 / 1000000000000) (9841473252 / 1000000000000)))) (orderedInterval (-3998313032 / 1000000000000) (-3998312846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (829772773470291 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42798234318 / 1000000000000) (42798234319 / 1000000000000), orderedInterval (35070650642 / 1000000000000) (35070650643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3372980256549811 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23943921037 / 1000000000000) (23943950302 / 1000000000000), orderedInterval (-13492045032 / 1000000000000) (-13492015767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2252994493763549 / 4000000000000) 4 (IntervalRat.scale (907 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33385933696 / 1000000000000) (-33385930659 / 1000000000000), orderedInterval (3984800104 / 1000000000000) (3984803141 / 1000000000000)))) (orderedInterval (-8357167864 / 1000000000000) (-8357137314 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate582_chunkChecks4 :
    compactCertificate582.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate582.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate582_chunkChecks4_0
    compactCertificate582_chunkChecks4_1 compactCertificate582_chunkChecks4_2

theorem compactCertificate582_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate582.chunkCheck r b = true :=
  compactCertificate582.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate582_chunkChecks0
    · exact compactCertificate582_chunkChecks1
    · exact compactCertificate582_chunkChecks2
    · exact compactCertificate582_chunkChecks3
    · exact compactCertificate582_chunkChecks4)

theorem compactCertificate582_coefficient0 :
    compactCertificate582.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate582_coefficient1 :
    compactCertificate582.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate582_coefficient2 :
    compactCertificate582.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate582_coefficient3 :
    compactCertificate582.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate582_coefficient4 :
    compactCertificate582.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate582_coefficients : ∀ r : Fin 5,
    compactCertificate582.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate582_coefficient0
  · exact compactCertificate582_coefficient1
  · exact compactCertificate582_coefficient2
  · exact compactCertificate582_coefficient3
  · exact compactCertificate582_coefficient4

theorem compactCertificate582_lower : (1 : ℚ) ≤ compactCertificate582.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate582, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate582_proves {t : ℝ} (ht : t ∈ compactCertificate582.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate582.proves compactCertificate582_states compactCertificate582_chunks
    compactCertificate582_coefficients compactCertificate582_lower ht

end Erdos232
