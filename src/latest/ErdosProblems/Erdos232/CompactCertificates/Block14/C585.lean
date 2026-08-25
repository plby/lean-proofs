/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate585 : CompactCertificate where
  left := 456
  right := 457
  center := 913 / 2
  grid := fun i =>
    match i.val with
    | 0 => 145
    | 1 => 107
    | 2 => 173
    | 3 => 31
    | 4 => 84
    | 5 => 228
    | 6 => 168
    | 7 => 288
    | 8 => 212
    | 9 => 325
    | 10 => 188
    | 11 => 333
    | 12 => 311
    | 13 => 222
    | 14 => 252
    | 15 => 210
    | 16 => 185
    | 17 => 269
    | 18 => 149
    | 19 => 126
    | 20 => 79
    | 21 => 42
    | 22 => 115
    | 23 => 157
    | 24 => 67
    | 25 => 270
    | _ => 181
  point := fun i =>
    match i.val with
    | 0 => 913 / 2
    | 1 => 1345023335433613 / 4000000000000
    | 2 => 434952911430829 / 800000000000
    | 3 => 392474454743591 / 4000000000000
    | 4 => 1054241591540027 / 4000000000000
    | 5 => 2862471000226959 / 4000000000000
    | 6 => 2108483183080967 / 4000000000000
    | 7 => 3612921872153891 / 4000000000000
    | 8 => 2661261898763369 / 4000000000000
    | 9 => 4083060126914087 / 4000000000000
    | 10 => 2357355863391023 / 4000000000000
    | 11 => 4183169347230907 / 4000000000000
    | 12 => 3908459430638983 / 4000000000000
    | 13 => 2789261072995639 / 4000000000000
    | 14 => 3162724774620081 / 4000000000000
    | 15 => 2636750186445089 / 4000000000000
    | 16 => 2329648754334869 / 4000000000000
    | 17 => 675223011428031 / 800000000000
    | 18 => 1867702384650157 / 4000000000000
    | 19 => 1583271995705477 / 4000000000000
    | 20 => 990738101236631 / 4000000000000
    | 21 => 532822245891177 / 4000000000000
    | 22 => 1446716046284531 / 4000000000000
    | 23 => 1975367077642387 / 4000000000000
    | 24 => 835261898763369 / 4000000000000
    | 25 => 3395293246119049 / 4000000000000
    | _ => 2267898536721191 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))
    | 1 => (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))
    | 2 => (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000))
    | 3 => (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))
    | 4 => (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))
    | 5 => (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000))
    | 6 => (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))
    | 7 => (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))
    | 8 => (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000))
    | 9 => (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))
    | 10 => (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))
    | 11 => (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000))
    | 12 => (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))
    | 13 => (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))
    | 14 => (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000))
    | 15 => (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))
    | 16 => (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))
    | 17 => (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000))
    | 18 => (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))
    | 19 => (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))
    | 20 => (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000))
    | 21 => (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))
    | 22 => (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))
    | 23 => (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000))
    | 24 => (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))
    | 25 => (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))
    | _ => (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16537268949 / 1000000000000) (-16537267555 / 1000000000000)
      | 1 => orderedInterval (1401960648 / 1000000000000) (1401960703 / 1000000000000)
      | 2 => orderedInterval (627895710 / 1000000000000) (627895767 / 1000000000000)
      | 3 => orderedInterval (-357139607 / 1000000000000) (-357139408 / 1000000000000)
      | 4 => orderedInterval (2148677977 / 1000000000000) (2148678032 / 1000000000000)
      | 5 => orderedInterval (1993497324 / 1000000000000) (1993501342 / 1000000000000)
      | 6 => orderedInterval (-4255495887 / 1000000000000) (-4255495751 / 1000000000000)
      | 7 => orderedInterval (2453772468 / 1000000000000) (2453772758 / 1000000000000)
      | _ => orderedInterval (-6729490954 / 1000000000000) (-6729486686 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1199021843 / 1000000000000) (1199023242 / 1000000000000)
      | 1 => orderedInterval (-2358601876 / 1000000000000) (-2358601813 / 1000000000000)
      | 2 => orderedInterval (-85950534 / 1000000000000) (-85950429 / 1000000000000)
      | 3 => orderedInterval (4001351391 / 1000000000000) (4001351790 / 1000000000000)
      | 4 => orderedInterval (3823897034 / 1000000000000) (3823897122 / 1000000000000)
      | 5 => orderedInterval (-1760623182 / 1000000000000) (-1760618048 / 1000000000000)
      | 6 => orderedInterval (3314757072 / 1000000000000) (3314757200 / 1000000000000)
      | 7 => orderedInterval (968543330 / 1000000000000) (968543451 / 1000000000000)
      | _ => orderedInterval (4163518038 / 1000000000000) (4163522869 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17088706516 / 1000000000000) (17088707923 / 1000000000000)
      | 1 => orderedInterval (326844146 / 1000000000000) (326844233 / 1000000000000)
      | 2 => orderedInterval (-2346885419 / 1000000000000) (-2346885221 / 1000000000000)
      | 3 => orderedInterval (-1720188206 / 1000000000000) (-1720187369 / 1000000000000)
      | 4 => orderedInterval (-5830727696 / 1000000000000) (-5830727549 / 1000000000000)
      | 5 => orderedInterval (-3620975952 / 1000000000000) (-3620969378 / 1000000000000)
      | 6 => orderedInterval (3636101091 / 1000000000000) (3636101215 / 1000000000000)
      | 7 => orderedInterval (-3629626432 / 1000000000000) (-3629626359 / 1000000000000)
      | _ => orderedInterval (14905582850 / 1000000000000) (14905588709 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-766173355 / 1000000000000) (-766171941 / 1000000000000)
      | 1 => orderedInterval (7797306952 / 1000000000000) (7797307082 / 1000000000000)
      | 2 => orderedInterval (2285933978 / 1000000000000) (2285934357 / 1000000000000)
      | 3 => orderedInterval (-8964127179 / 1000000000000) (-8964125374 / 1000000000000)
      | 4 => orderedInterval (-10185405800 / 1000000000000) (-10185405552 / 1000000000000)
      | 5 => orderedInterval (4884892140 / 1000000000000) (4884900552 / 1000000000000)
      | 6 => orderedInterval (-4540326261 / 1000000000000) (-4540326140 / 1000000000000)
      | 7 => orderedInterval (-785279704 / 1000000000000) (-785279643 / 1000000000000)
      | _ => orderedInterval (-5071890991 / 1000000000000) (-5071883667 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18000104229 / 1000000000000) (-18000102804 / 1000000000000)
      | 1 => orderedInterval (-1476241521 / 1000000000000) (-1476241322 / 1000000000000)
      | 2 => orderedInterval (8942550755 / 1000000000000) (8942551486 / 1000000000000)
      | 3 => orderedInterval (13133009324 / 1000000000000) (13133013294 / 1000000000000)
      | 4 => orderedInterval (17303185811 / 1000000000000) (17303186241 / 1000000000000)
      | 5 => orderedInterval (7126044735 / 1000000000000) (7126055531 / 1000000000000)
      | 6 => orderedInterval (-3342578676 / 1000000000000) (-3342578555 / 1000000000000)
      | 7 => orderedInterval (4053848847 / 1000000000000) (4053848907 / 1000000000000)
      | _ => orderedInterval (-37543679173 / 1000000000000) (-37543669824 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-19253591270 / 1000000000000) (-19253580798 / 1000000000000)
    | 1 => orderedInterval (13265913116 / 1000000000000) (13265925384 / 1000000000000)
    | 2 => orderedInterval (18808830898 / 1000000000000) (18808846204 / 1000000000000)
    | 3 => orderedInterval (-15345070220 / 1000000000000) (-15345050326 / 1000000000000)
    | _ => orderedInterval (-9803964127 / 1000000000000) (-9803937046 / 1000000000000)

theorem compactCertificate585_stateChecks0 :
    compactCertificate585.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (913 / 2)) (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1345023335433613 / 4000000000000)) (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (434952911430829 / 800000000000)) (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks1 :
    compactCertificate585.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (392474454743591 / 4000000000000)) (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1054241591540027 / 4000000000000)) (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2862471000226959 / 4000000000000)) (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks2 :
    compactCertificate585.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2108483183080967 / 4000000000000)) (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (3612921872153891 / 4000000000000)) (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2661261898763369 / 4000000000000)) (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks3 :
    compactCertificate585.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 325 12 (4083060126914087 / 4000000000000)) (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2357355863391023 / 4000000000000)) (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 333 12 (4183169347230907 / 4000000000000)) (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks4 :
    compactCertificate585.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 311 12 (3908459430638983 / 4000000000000)) (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2789261072995639 / 4000000000000)) (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3162724774620081 / 4000000000000)) (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks5 :
    compactCertificate585.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2636750186445089 / 4000000000000)) (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2329648754334869 / 4000000000000)) (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (675223011428031 / 800000000000)) (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks6 :
    compactCertificate585.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1867702384650157 / 4000000000000)) (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1583271995705477 / 4000000000000)) (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (990738101236631 / 4000000000000)) (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks7 :
    compactCertificate585.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (532822245891177 / 4000000000000)) (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1446716046284531 / 4000000000000)) (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1975367077642387 / 4000000000000)) (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_stateChecks8 :
    compactCertificate585.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (835261898763369 / 4000000000000)) (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3395293246119049 / 4000000000000)) (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2267898536721191 / 4000000000000)) (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_states : ∀ j,
    BesselStateValid (compactCertificate585.point j) (compactCertificate585.state j) :=
  compactCertificate585.statesValid_of_checks3 compactCertificate585_stateChecks0
    compactCertificate585_stateChecks1 compactCertificate585_stateChecks2
    compactCertificate585_stateChecks3 compactCertificate585_stateChecks4
    compactCertificate585_stateChecks5 compactCertificate585_stateChecks6
    compactCertificate585_stateChecks7 compactCertificate585_stateChecks8

theorem compactCertificate585_chunkChecks0_0 :
    compactCertificate585.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (913 / 2) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1345023335433613 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (434952911430829 / 800000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000)))) (orderedInterval (-16537268949 / 1000000000000) (-16537267555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (392474454743591 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1054241591540027 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2862471000226959 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000)))) (orderedInterval (1401960648 / 1000000000000) (1401960703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2108483183080967 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3612921872153891 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2661261898763369 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000)))) (orderedInterval (627895710 / 1000000000000) (627895767 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks0_1 :
    compactCertificate585.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4083060126914087 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2357355863391023 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4183169347230907 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000)))) (orderedInterval (-357139607 / 1000000000000) (-357139408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3908459430638983 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2789261072995639 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3162724774620081 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000)))) (orderedInterval (2148677977 / 1000000000000) (2148678032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2636750186445089 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2329648754334869 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (675223011428031 / 800000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000)))) (orderedInterval (1993497324 / 1000000000000) (1993501342 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks0_2 :
    compactCertificate585.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1867702384650157 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1583271995705477 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (990738101236631 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000)))) (orderedInterval (-4255495887 / 1000000000000) (-4255495751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (532822245891177 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1446716046284531 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1975367077642387 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000)))) (orderedInterval (2453772468 / 1000000000000) (2453772758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (835261898763369 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3395293246119049 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2267898536721191 / 4000000000000) 0 (IntervalRat.scale (913 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000)))) (orderedInterval (-6729490954 / 1000000000000) (-6729486686 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks0 :
    compactCertificate585.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate585.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate585_chunkChecks0_0
    compactCertificate585_chunkChecks0_1 compactCertificate585_chunkChecks0_2

theorem compactCertificate585_chunkChecks1_0 :
    compactCertificate585.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (913 / 2) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1345023335433613 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (434952911430829 / 800000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000)))) (orderedInterval (1199021843 / 1000000000000) (1199023242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (392474454743591 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1054241591540027 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2862471000226959 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000)))) (orderedInterval (-2358601876 / 1000000000000) (-2358601813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2108483183080967 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3612921872153891 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2661261898763369 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000)))) (orderedInterval (-85950534 / 1000000000000) (-85950429 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks1_1 :
    compactCertificate585.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4083060126914087 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2357355863391023 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4183169347230907 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000)))) (orderedInterval (4001351391 / 1000000000000) (4001351790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3908459430638983 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2789261072995639 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3162724774620081 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000)))) (orderedInterval (3823897034 / 1000000000000) (3823897122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2636750186445089 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2329648754334869 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (675223011428031 / 800000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000)))) (orderedInterval (-1760623182 / 1000000000000) (-1760618048 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks1_2 :
    compactCertificate585.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1867702384650157 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1583271995705477 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (990738101236631 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000)))) (orderedInterval (3314757072 / 1000000000000) (3314757200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (532822245891177 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1446716046284531 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1975367077642387 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000)))) (orderedInterval (968543330 / 1000000000000) (968543451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (835261898763369 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3395293246119049 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2267898536721191 / 4000000000000) 1 (IntervalRat.scale (913 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000)))) (orderedInterval (4163518038 / 1000000000000) (4163522869 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks1 :
    compactCertificate585.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate585.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate585_chunkChecks1_0
    compactCertificate585_chunkChecks1_1 compactCertificate585_chunkChecks1_2

theorem compactCertificate585_chunkChecks2_0 :
    compactCertificate585.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (913 / 2) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1345023335433613 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (434952911430829 / 800000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000)))) (orderedInterval (17088706516 / 1000000000000) (17088707923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (392474454743591 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1054241591540027 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2862471000226959 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000)))) (orderedInterval (326844146 / 1000000000000) (326844233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2108483183080967 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3612921872153891 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2661261898763369 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000)))) (orderedInterval (-2346885419 / 1000000000000) (-2346885221 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks2_1 :
    compactCertificate585.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4083060126914087 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2357355863391023 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4183169347230907 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000)))) (orderedInterval (-1720188206 / 1000000000000) (-1720187369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3908459430638983 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2789261072995639 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3162724774620081 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000)))) (orderedInterval (-5830727696 / 1000000000000) (-5830727549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2636750186445089 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2329648754334869 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (675223011428031 / 800000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000)))) (orderedInterval (-3620975952 / 1000000000000) (-3620969378 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks2_2 :
    compactCertificate585.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1867702384650157 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1583271995705477 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (990738101236631 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000)))) (orderedInterval (3636101091 / 1000000000000) (3636101215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (532822245891177 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1446716046284531 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1975367077642387 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000)))) (orderedInterval (-3629626432 / 1000000000000) (-3629626359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (835261898763369 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3395293246119049 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2267898536721191 / 4000000000000) 2 (IntervalRat.scale (913 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000)))) (orderedInterval (14905582850 / 1000000000000) (14905588709 / 1000000000000))) = true
  rfl'

theorem compactCertificate585_chunkChecks2 :
    compactCertificate585.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate585.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate585_chunkChecks2_0
    compactCertificate585_chunkChecks2_1 compactCertificate585_chunkChecks2_2

theorem compactCertificate585_chunkChecks3_0 :
    compactCertificate585.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (913 / 2) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1345023335433613 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (434952911430829 / 800000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000)))) (orderedInterval (-766173355 / 1000000000000) (-766171941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (392474454743591 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1054241591540027 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2862471000226959 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000)))) (orderedInterval (7797306952 / 1000000000000) (7797307082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2108483183080967 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3612921872153891 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2661261898763369 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000)))) (orderedInterval (2285933978 / 1000000000000) (2285934357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate585_chunkChecks3_1 :
    compactCertificate585.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4083060126914087 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2357355863391023 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4183169347230907 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000)))) (orderedInterval (-8964127179 / 1000000000000) (-8964125374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3908459430638983 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2789261072995639 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3162724774620081 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000)))) (orderedInterval (-10185405800 / 1000000000000) (-10185405552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2636750186445089 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2329648754334869 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (675223011428031 / 800000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000)))) (orderedInterval (4884892140 / 1000000000000) (4884900552 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate585_chunkChecks3_2 :
    compactCertificate585.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1867702384650157 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1583271995705477 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (990738101236631 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000)))) (orderedInterval (-4540326261 / 1000000000000) (-4540326140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (532822245891177 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1446716046284531 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1975367077642387 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000)))) (orderedInterval (-785279704 / 1000000000000) (-785279643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (835261898763369 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3395293246119049 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2267898536721191 / 4000000000000) 3 (IntervalRat.scale (913 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000)))) (orderedInterval (-5071890991 / 1000000000000) (-5071883667 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate585_chunkChecks3 :
    compactCertificate585.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate585.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate585_chunkChecks3_0
    compactCertificate585_chunkChecks3_1 compactCertificate585_chunkChecks3_2

theorem compactCertificate585_chunkChecks4_0 :
    compactCertificate585.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (913 / 2) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36717653503 / 1000000000000) (-36717650066 / 1000000000000), orderedInterval (6850510161 / 1000000000000) (6850513599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1345023335433613 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33823844348 / 1000000000000) (-33823844347 / 1000000000000), orderedInterval (-27321356201 / 1000000000000) (-27321356200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (434952911430829 / 800000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28433391865 / 1000000000000) (-28433391864 / 1000000000000), orderedInterval (-19012332943 / 1000000000000) (-19012332942 / 1000000000000)))) (orderedInterval (-18000104229 / 1000000000000) (-18000102804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (392474454743591 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80416456962 / 1000000000000) (-80416456948 / 1000000000000), orderedInterval (-4213731313 / 1000000000000) (-4213731299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1054241591540027 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21445455019 / 1000000000000) (21445455020 / 1000000000000), orderedInterval (44180982749 / 1000000000000) (44180982750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2862471000226959 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3566087407 / 1000000000000) (3566087408 / 1000000000000), orderedInterval (29609869420 / 1000000000000) (29609869421 / 1000000000000)))) (orderedInterval (-1476241521 / 1000000000000) (-1476241322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2108483183080967 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4104767255 / 1000000000000) (4104767256 / 1000000000000), orderedInterval (34505260917 / 1000000000000) (34505260918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3612921872153891 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18346674533 / 1000000000000) (-18346673553 / 1000000000000), orderedInterval (19199344060 / 1000000000000) (19199345040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2661261898763369 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2565824093 / 1000000000000) (2565824094 / 1000000000000), orderedInterval (30824778366 / 1000000000000) (30824778367 / 1000000000000)))) (orderedInterval (8942550755 / 1000000000000) (8942551486 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate585_chunkChecks4_1 :
    compactCertificate585.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4083060126914087 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12682895115 / 1000000000000) (-12682895114 / 1000000000000), orderedInterval (-21506887475 / 1000000000000) (-21506887474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2357355863391023 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15620490337 / 1000000000000) (-15620490086 / 1000000000000), orderedInterval (28930848177 / 1000000000000) (28930848429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4183169347230907 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10223895978 / 1000000000000) (-10223895977 / 1000000000000), orderedInterval (-22449865519 / 1000000000000) (-22449865518 / 1000000000000)))) (orderedInterval (13133009324 / 1000000000000) (13133013294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3908459430638983 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19423919965 / 1000000000000) (-19423919964 / 1000000000000), orderedInterval (-16550297650 / 1000000000000) (-16550297649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2789261072995639 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18690133762 / 1000000000000) (18690133763 / 1000000000000), orderedInterval (23727644615 / 1000000000000) (23727644616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3162724774620081 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6051424269 / 1000000000000) (-6051424268 / 1000000000000), orderedInterval (27726271838 / 1000000000000) (27726271839 / 1000000000000)))) (orderedInterval (17303185811 / 1000000000000) (17303186241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2636750186445089 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7335633036 / 1000000000000) (7335633037 / 1000000000000), orderedInterval (30192995318 / 1000000000000) (30192995319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2329648754334869 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30025233529 / 1000000000000) (-30025164085 / 1000000000000), orderedInterval (13866311241 / 1000000000000) (13866380684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (675223011428031 / 800000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7442113794 / 1000000000000) (7442113796 / 1000000000000), orderedInterval (-26440712870 / 1000000000000) (-26440712869 / 1000000000000)))) (orderedInterval (7126044735 / 1000000000000) (7126055531 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate585_chunkChecks4_2 :
    compactCertificate585.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1867702384650157 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13921391063 / 1000000000000) (13921391197 / 1000000000000), orderedInterval (-34214675944 / 1000000000000) (-34214675810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1583271995705477 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27698674715 / 1000000000000) (27698674716 / 1000000000000), orderedInterval (28967568859 / 1000000000000) (28967568860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (990738101236631 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14185930909 / 1000000000000) (-14185930908 / 1000000000000), orderedInterval (-48644236250 / 1000000000000) (-48644236249 / 1000000000000)))) (orderedInterval (-3342578676 / 1000000000000) (-3342578555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (532822245891177 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61562414983 / 1000000000000) (61562427514 / 1000000000000), orderedInterval (-31683852580 / 1000000000000) (-31683840049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1446716046284531 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38805862311 / 1000000000000) (-38805862310 / 1000000000000), orderedInterval (-15892599714 / 1000000000000) (-15892599713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1975367077642387 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35362560582 / 1000000000000) (-35362560534 / 1000000000000), orderedInterval (-6177536418 / 1000000000000) (-6177536371 / 1000000000000)))) (orderedInterval (4053848847 / 1000000000000) (4053848907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (835261898763369 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42781843184 / 1000000000000) (42781951260 / 1000000000000), orderedInterval (-35008459652 / 1000000000000) (-35008351576 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3395293246119049 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26881632092 / 1000000000000) (26881632526 / 1000000000000), orderedInterval (5216795445 / 1000000000000) (5216795879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2267898536721191 / 4000000000000) 4 (IntervalRat.scale (913 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25578354192 / 1000000000000) (25578372600 / 1000000000000), orderedInterval (-21669359390 / 1000000000000) (-21669340981 / 1000000000000)))) (orderedInterval (-37543679173 / 1000000000000) (-37543669824 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate585_chunkChecks4 :
    compactCertificate585.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate585.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate585_chunkChecks4_0
    compactCertificate585_chunkChecks4_1 compactCertificate585_chunkChecks4_2

theorem compactCertificate585_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate585.chunkCheck r b = true :=
  compactCertificate585.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate585_chunkChecks0
    · exact compactCertificate585_chunkChecks1
    · exact compactCertificate585_chunkChecks2
    · exact compactCertificate585_chunkChecks3
    · exact compactCertificate585_chunkChecks4)

theorem compactCertificate585_coefficient0 :
    compactCertificate585.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate585_coefficient1 :
    compactCertificate585.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate585_coefficient2 :
    compactCertificate585.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate585_coefficient3 :
    compactCertificate585.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate585_coefficient4 :
    compactCertificate585.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate585_coefficients : ∀ r : Fin 5,
    compactCertificate585.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate585_coefficient0
  · exact compactCertificate585_coefficient1
  · exact compactCertificate585_coefficient2
  · exact compactCertificate585_coefficient3
  · exact compactCertificate585_coefficient4

theorem compactCertificate585_lower : (1 : ℚ) ≤ compactCertificate585.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate585, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate585_proves {t : ℝ} (ht : t ∈ compactCertificate585.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate585.proves compactCertificate585_states compactCertificate585_chunks
    compactCertificate585_coefficients compactCertificate585_lower ht

end Erdos232
