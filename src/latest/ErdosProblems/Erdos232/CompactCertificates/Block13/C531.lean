/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate531 : CompactCertificate where
  left := 402
  right := 403
  center := 805 / 2
  grid := fun i =>
    match i.val with
    | 0 => 128
    | 1 => 94
    | 2 => 153
    | 3 => 28
    | 4 => 74
    | 5 => 201
    | 6 => 148
    | 7 => 254
    | 8 => 187
    | 9 => 287
    | 10 => 165
    | 11 => 294
    | 12 => 274
    | 13 => 196
    | 14 => 222
    | 15 => 185
    | 16 => 164
    | 17 => 237
    | 18 => 131
    | 19 => 111
    | 20 => 70
    | 21 => 37
    | 22 => 102
    | 23 => 139
    | 24 => 59
    | 25 => 238
    | _ => 159
  point := fun i =>
    match i.val with
    | 0 => 805 / 2
    | 1 => 237183742612061 / 800000000000
    | 2 => 76700349113213 / 160000000000
    | 3 => 69209624549527 / 800000000000
    | 4 => 185906786679019 / 800000000000
    | 5 => 504773089853823 / 800000000000
    | 6 => 371813573358199 / 800000000000
    | 7 => 637108895308627 / 800000000000
    | 8 => 469291528697593 / 800000000000
    | 9 => 720013888754839 / 800000000000
    | 10 => 415700212492831 / 800000000000
    | 11 => 737667321910379 / 800000000000
    | 12 => 689224499816951 / 800000000000
    | 13 => 491863124591783 / 800000000000
    | 14 => 557720360037057 / 800000000000
    | 15 => 464969090928433 / 800000000000
    | 16 => 410814292933093 / 800000000000
    | 17 => 119069994348207 / 160000000000
    | 18 => 329353870677629 / 800000000000
    | 19 => 279196923667669 / 800000000000
    | 20 => 174708471302407 / 800000000000
    | 21 => 93958796920569 / 800000000000
    | 22 => 255116411228707 / 800000000000
    | 23 => 348339648959939 / 800000000000
    | 24 => 147291528697593 / 800000000000
    | 25 => 598731886774553 / 800000000000
    | _ => 399925152696727 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))
    | 1 => (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))
    | 2 => (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000))
    | 3 => (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))
    | 4 => (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))
    | 5 => (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000))
    | 6 => (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))
    | 7 => (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))
    | 8 => (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000))
    | 9 => (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))
    | 10 => (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))
    | 11 => (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000))
    | 12 => (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))
    | 13 => (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))
    | 14 => (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000))
    | 15 => (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))
    | 16 => (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))
    | 17 => (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000))
    | 18 => (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))
    | 19 => (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))
    | 20 => (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000))
    | 21 => (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))
    | 22 => (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))
    | 23 => (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000))
    | 24 => (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))
    | 25 => (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))
    | _ => (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15887821054 / 1000000000000) (15887821225 / 1000000000000)
      | 1 => orderedInterval (2442910729 / 1000000000000) (2442911076 / 1000000000000)
      | 2 => orderedInterval (683640033 / 1000000000000) (683640136 / 1000000000000)
      | 3 => orderedInterval (-8375714659 / 1000000000000) (-8375708222 / 1000000000000)
      | 4 => orderedInterval (-982461001 / 1000000000000) (-982460908 / 1000000000000)
      | 5 => orderedInterval (1024088078 / 1000000000000) (1024090262 / 1000000000000)
      | 6 => orderedInterval (5963105728 / 1000000000000) (5963106777 / 1000000000000)
      | 7 => orderedInterval (607713506 / 1000000000000) (607714224 / 1000000000000)
      | _ => orderedInterval (3973980545 / 1000000000000) (3973980754 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3904849302 / 1000000000000) (3904849454 / 1000000000000)
      | 1 => orderedInterval (4081172453 / 1000000000000) (4081172573 / 1000000000000)
      | 2 => orderedInterval (-2368224104 / 1000000000000) (-2368223907 / 1000000000000)
      | 3 => orderedInterval (14853009961 / 1000000000000) (14853018897 / 1000000000000)
      | 4 => orderedInterval (4319007580 / 1000000000000) (4319007755 / 1000000000000)
      | 5 => orderedInterval (-3213051899 / 1000000000000) (-3213049106 / 1000000000000)
      | 6 => orderedInterval (5563767476 / 1000000000000) (5563768084 / 1000000000000)
      | 7 => orderedInterval (2079266094 / 1000000000000) (2079266614 / 1000000000000)
      | _ => orderedInterval (2722089803 / 1000000000000) (2722090123 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16144509484 / 1000000000000) (-16144509340 / 1000000000000)
      | 1 => orderedInterval (-2036946349 / 1000000000000) (-2036946258 / 1000000000000)
      | 2 => orderedInterval (-2559044867 / 1000000000000) (-2559044485 / 1000000000000)
      | 3 => orderedInterval (34799246339 / 1000000000000) (34799259305 / 1000000000000)
      | 4 => orderedInterval (3432578902 / 1000000000000) (3432579238 / 1000000000000)
      | 5 => orderedInterval (-992323242 / 1000000000000) (-992319660 / 1000000000000)
      | 6 => orderedInterval (-6522176298 / 1000000000000) (-6522175928 / 1000000000000)
      | 7 => orderedInterval (1008419849 / 1000000000000) (1008420264 / 1000000000000)
      | _ => orderedInterval (-1394242413 / 1000000000000) (-1394241884 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2984277478 / 1000000000000) (-2984277335 / 1000000000000)
      | 1 => orderedInterval (-8600758971 / 1000000000000) (-8600758853 / 1000000000000)
      | 2 => orderedInterval (7205889053 / 1000000000000) (7205889798 / 1000000000000)
      | 3 => orderedInterval (-70761605300 / 1000000000000) (-70761585388 / 1000000000000)
      | 4 => orderedInterval (-9811722463 / 1000000000000) (-9811721802 / 1000000000000)
      | 5 => orderedInterval (7675861177 / 1000000000000) (7675865768 / 1000000000000)
      | 6 => orderedInterval (-4975986674 / 1000000000000) (-4975986435 / 1000000000000)
      | 7 => orderedInterval (-2929993130 / 1000000000000) (-2929992783 / 1000000000000)
      | _ => orderedInterval (-3806458264 / 1000000000000) (-3806457358 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16660274237 / 1000000000000) (16660274386 / 1000000000000)
      | 1 => orderedInterval (4097397162 / 1000000000000) (4097397339 / 1000000000000)
      | 2 => orderedInterval (9768826367 / 1000000000000) (9768827827 / 1000000000000)
      | 3 => orderedInterval (-164376170630 / 1000000000000) (-164376137724 / 1000000000000)
      | 4 => orderedInterval (-13180892487 / 1000000000000) (-13180891161 / 1000000000000)
      | 5 => orderedInterval (-521260024 / 1000000000000) (-521254116 / 1000000000000)
      | 6 => orderedInterval (6628452187 / 1000000000000) (6628452355 / 1000000000000)
      | 7 => orderedInterval (-1524479331 / 1000000000000) (-1524479031 / 1000000000000)
      | _ => orderedInterval (-13563814837 / 1000000000000) (-13563813245 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21225084013 / 1000000000000) (21225095324 / 1000000000000)
    | 1 => orderedInterval (31941886666 / 1000000000000) (31941900487 / 1000000000000)
    | 2 => orderedInterval (9591002437 / 1000000000000) (9591021252 / 1000000000000)
    | 3 => orderedInterval (-88989052050 / 1000000000000) (-88989024388 / 1000000000000)
    | _ => orderedInterval (-156011667356 / 1000000000000) (-156011623370 / 1000000000000)

theorem compactCertificate531_stateChecks0 :
    compactCertificate531.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (805 / 2)) (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (237183742612061 / 800000000000)) (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (76700349113213 / 160000000000)) (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks1 :
    compactCertificate531.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (69209624549527 / 800000000000)) (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (185906786679019 / 800000000000)) (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (504773089853823 / 800000000000)) (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks2 :
    compactCertificate531.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (371813573358199 / 800000000000)) (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (637108895308627 / 800000000000)) (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (469291528697593 / 800000000000)) (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks3 :
    compactCertificate531.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (720013888754839 / 800000000000)) (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (415700212492831 / 800000000000)) (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (737667321910379 / 800000000000)) (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks4 :
    compactCertificate531.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (689224499816951 / 800000000000)) (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (491863124591783 / 800000000000)) (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (557720360037057 / 800000000000)) (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks5 :
    compactCertificate531.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (464969090928433 / 800000000000)) (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (410814292933093 / 800000000000)) (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (119069994348207 / 160000000000)) (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks6 :
    compactCertificate531.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (329353870677629 / 800000000000)) (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (279196923667669 / 800000000000)) (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (174708471302407 / 800000000000)) (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks7 :
    compactCertificate531.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (93958796920569 / 800000000000)) (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (255116411228707 / 800000000000)) (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (348339648959939 / 800000000000)) (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_stateChecks8 :
    compactCertificate531.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (147291528697593 / 800000000000)) (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (598731886774553 / 800000000000)) (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (399925152696727 / 800000000000)) (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_states : ∀ j,
    BesselStateValid (compactCertificate531.point j) (compactCertificate531.state j) :=
  compactCertificate531.statesValid_of_checks3 compactCertificate531_stateChecks0
    compactCertificate531_stateChecks1 compactCertificate531_stateChecks2
    compactCertificate531_stateChecks3 compactCertificate531_stateChecks4
    compactCertificate531_stateChecks5 compactCertificate531_stateChecks6
    compactCertificate531_stateChecks7 compactCertificate531_stateChecks8

theorem compactCertificate531_chunkChecks0_0 :
    compactCertificate531.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (805 / 2) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (237183742612061 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (76700349113213 / 160000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000)))) (orderedInterval (15887821054 / 1000000000000) (15887821225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (69209624549527 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (185906786679019 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (504773089853823 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000)))) (orderedInterval (2442910729 / 1000000000000) (2442911076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (371813573358199 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (637108895308627 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (469291528697593 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000)))) (orderedInterval (683640033 / 1000000000000) (683640136 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks0_1 :
    compactCertificate531.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (720013888754839 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (415700212492831 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (737667321910379 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000)))) (orderedInterval (-8375714659 / 1000000000000) (-8375708222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (689224499816951 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (491863124591783 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (557720360037057 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000)))) (orderedInterval (-982461001 / 1000000000000) (-982460908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (464969090928433 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (410814292933093 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (119069994348207 / 160000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000)))) (orderedInterval (1024088078 / 1000000000000) (1024090262 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks0_2 :
    compactCertificate531.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (329353870677629 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (279196923667669 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (174708471302407 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000)))) (orderedInterval (5963105728 / 1000000000000) (5963106777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (93958796920569 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (255116411228707 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (348339648959939 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000)))) (orderedInterval (607713506 / 1000000000000) (607714224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (147291528697593 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (598731886774553 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (399925152696727 / 800000000000) 0 (IntervalRat.scale (805 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000)))) (orderedInterval (3973980545 / 1000000000000) (3973980754 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks0 :
    compactCertificate531.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate531.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate531_chunkChecks0_0
    compactCertificate531_chunkChecks0_1 compactCertificate531_chunkChecks0_2

theorem compactCertificate531_chunkChecks1_0 :
    compactCertificate531.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (805 / 2) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (237183742612061 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (76700349113213 / 160000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000)))) (orderedInterval (3904849302 / 1000000000000) (3904849454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (69209624549527 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (185906786679019 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (504773089853823 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000)))) (orderedInterval (4081172453 / 1000000000000) (4081172573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (371813573358199 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (637108895308627 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (469291528697593 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000)))) (orderedInterval (-2368224104 / 1000000000000) (-2368223907 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks1_1 :
    compactCertificate531.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (720013888754839 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (415700212492831 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (737667321910379 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000)))) (orderedInterval (14853009961 / 1000000000000) (14853018897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (689224499816951 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (491863124591783 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (557720360037057 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000)))) (orderedInterval (4319007580 / 1000000000000) (4319007755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (464969090928433 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (410814292933093 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (119069994348207 / 160000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000)))) (orderedInterval (-3213051899 / 1000000000000) (-3213049106 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks1_2 :
    compactCertificate531.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (329353870677629 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (279196923667669 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (174708471302407 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000)))) (orderedInterval (5563767476 / 1000000000000) (5563768084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (93958796920569 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (255116411228707 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (348339648959939 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000)))) (orderedInterval (2079266094 / 1000000000000) (2079266614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (147291528697593 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (598731886774553 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (399925152696727 / 800000000000) 1 (IntervalRat.scale (805 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000)))) (orderedInterval (2722089803 / 1000000000000) (2722090123 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks1 :
    compactCertificate531.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate531.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate531_chunkChecks1_0
    compactCertificate531_chunkChecks1_1 compactCertificate531_chunkChecks1_2

theorem compactCertificate531_chunkChecks2_0 :
    compactCertificate531.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (805 / 2) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (237183742612061 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (76700349113213 / 160000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000)))) (orderedInterval (-16144509484 / 1000000000000) (-16144509340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (69209624549527 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (185906786679019 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (504773089853823 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000)))) (orderedInterval (-2036946349 / 1000000000000) (-2036946258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (371813573358199 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (637108895308627 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (469291528697593 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000)))) (orderedInterval (-2559044867 / 1000000000000) (-2559044485 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks2_1 :
    compactCertificate531.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (720013888754839 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (415700212492831 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (737667321910379 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000)))) (orderedInterval (34799246339 / 1000000000000) (34799259305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (689224499816951 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (491863124591783 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (557720360037057 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000)))) (orderedInterval (3432578902 / 1000000000000) (3432579238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (464969090928433 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (410814292933093 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (119069994348207 / 160000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000)))) (orderedInterval (-992323242 / 1000000000000) (-992319660 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks2_2 :
    compactCertificate531.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (329353870677629 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (279196923667669 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (174708471302407 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000)))) (orderedInterval (-6522176298 / 1000000000000) (-6522175928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (93958796920569 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (255116411228707 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (348339648959939 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000)))) (orderedInterval (1008419849 / 1000000000000) (1008420264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (147291528697593 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (598731886774553 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (399925152696727 / 800000000000) 2 (IntervalRat.scale (805 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000)))) (orderedInterval (-1394242413 / 1000000000000) (-1394241884 / 1000000000000))) = true
  rfl'

theorem compactCertificate531_chunkChecks2 :
    compactCertificate531.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate531.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate531_chunkChecks2_0
    compactCertificate531_chunkChecks2_1 compactCertificate531_chunkChecks2_2

theorem compactCertificate531_chunkChecks3_0 :
    compactCertificate531.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (805 / 2) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (237183742612061 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (76700349113213 / 160000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000)))) (orderedInterval (-2984277478 / 1000000000000) (-2984277335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (69209624549527 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (185906786679019 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (504773089853823 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000)))) (orderedInterval (-8600758971 / 1000000000000) (-8600758853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (371813573358199 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (637108895308627 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (469291528697593 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000)))) (orderedInterval (7205889053 / 1000000000000) (7205889798 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate531_chunkChecks3_1 :
    compactCertificate531.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (720013888754839 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (415700212492831 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (737667321910379 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000)))) (orderedInterval (-70761605300 / 1000000000000) (-70761585388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (689224499816951 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (491863124591783 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (557720360037057 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000)))) (orderedInterval (-9811722463 / 1000000000000) (-9811721802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (464969090928433 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (410814292933093 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (119069994348207 / 160000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000)))) (orderedInterval (7675861177 / 1000000000000) (7675865768 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate531_chunkChecks3_2 :
    compactCertificate531.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (329353870677629 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (279196923667669 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (174708471302407 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000)))) (orderedInterval (-4975986674 / 1000000000000) (-4975986435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (93958796920569 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (255116411228707 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (348339648959939 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000)))) (orderedInterval (-2929993130 / 1000000000000) (-2929992783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (147291528697593 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (598731886774553 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (399925152696727 / 800000000000) 3 (IntervalRat.scale (805 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000)))) (orderedInterval (-3806458264 / 1000000000000) (-3806457358 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate531_chunkChecks3 :
    compactCertificate531.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate531.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate531_chunkChecks3_0
    compactCertificate531_chunkChecks3_1 compactCertificate531_chunkChecks3_2

theorem compactCertificate531_chunkChecks4_0 :
    compactCertificate531.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (805 / 2) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36480848341 / 1000000000000) (36480848342 / 1000000000000), orderedInterval (15791692748 / 1000000000000) (15791692750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (237183742612061 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42961267673 / 1000000000000) (42961279500 / 1000000000000), orderedInterval (-17438790756 / 1000000000000) (-17438778929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (76700349113213 / 160000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17514557499 / 1000000000000) (17514558054 / 1000000000000), orderedInterval (-31975348805 / 1000000000000) (-31975348250 / 1000000000000)))) (orderedInterval (16660274237 / 1000000000000) (16660274386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (69209624549527 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-53176183382 / 1000000000000) (-53176155936 / 1000000000000), orderedInterval (67620502625 / 1000000000000) (67620530071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (185906786679019 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33336267441 / 1000000000000) (33336267442 / 1000000000000), orderedInterval (40279443623 / 1000000000000) (40279443624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (504773089853823 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9126812645 / 1000000000000) (-9126812644 / 1000000000000), orderedInterval (-30417452944 / 1000000000000) (-30417452943 / 1000000000000)))) (orderedInterval (4097397162 / 1000000000000) (4097397339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (371813573358199 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20786957581 / 1000000000000) (20786957582 / 1000000000000), orderedInterval (30598935688 / 1000000000000) (30598935689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (637108895308627 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20147165111 / 1000000000000) (-20147162528 / 1000000000000), orderedInterval (19848917824 / 1000000000000) (19848920407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (469291528697593 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2574514807 / 1000000000000) (2574514808 / 1000000000000), orderedInterval (-32844488265 / 1000000000000) (-32844488264 / 1000000000000)))) (orderedInterval (9768826367 / 1000000000000) (9768827827 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate531_chunkChecks4_1 :
    compactCertificate531.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (720013888754839 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19706002589 / 1000000000000) (19706004868 / 1000000000000), orderedInterval (-17871941482 / 1000000000000) (-17871939203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (415700212492831 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31097710970 / 1000000000000) (-31097633301 / 1000000000000), orderedInterval (16094941301 / 1000000000000) (16095018969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (737667321910379 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18079524731 / 1000000000000) (-18079523899 / 1000000000000), orderedInterval (19076653146 / 1000000000000) (19076653977 / 1000000000000)))) (orderedInterval (-164376170630 / 1000000000000) (-164376137724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (689224499816951 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27147685252 / 1000000000000) (27147687743 / 1000000000000), orderedInterval (1378294327 / 1000000000000) (1378296818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (491863124591783 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4428418512 / 1000000000000) (-4428418510 / 1000000000000), orderedInterval (31875714580 / 1000000000000) (31875714582 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (557720360037057 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14543302860 / 1000000000000) (14543302861 / 1000000000000), orderedInterval (26478560050 / 1000000000000) (26478560051 / 1000000000000)))) (orderedInterval (-13180892487 / 1000000000000) (-13180891161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (464969090928433 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23785378300 / 1000000000000) (-23785378299 / 1000000000000), orderedInterval (-22992325803 / 1000000000000) (-22992325802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (410814292933093 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27973912466 / 1000000000000) (-27973874983 / 1000000000000), orderedInterval (21409075614 / 1000000000000) (21409113097 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (119069994348207 / 160000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11798886941 / 1000000000000) (-11798886940 / 1000000000000), orderedInterval (-26754781513 / 1000000000000) (-26754781512 / 1000000000000)))) (orderedInterval (-521260024 / 1000000000000) (-521254116 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate531_chunkChecks4_2 :
    compactCertificate531.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (329353870677629 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31494254316 / 1000000000000) (-31494254315 / 1000000000000), orderedInterval (-23508724276 / 1000000000000) (-23508724275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (279196923667669 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37350015673 / 1000000000000) (-37350015672 / 1000000000000), orderedInterval (-20661722014 / 1000000000000) (-20661722013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (174708471302407 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36448681284 / 1000000000000) (-36448652160 / 1000000000000), orderedInterval (39915750492 / 1000000000000) (39915779615 / 1000000000000)))) (orderedInterval (6628452187 / 1000000000000) (6628452355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (93958796920569 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-67130928092 / 1000000000000) (-67130921019 / 1000000000000), orderedInterval (30515284381 / 1000000000000) (30515291453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (255116411228707 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30843654306 / 1000000000000) (-30843632250 / 1000000000000), orderedInterval (32374760629 / 1000000000000) (32374782685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (348339648959939 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17375151414 / 1000000000000) (17375151920 / 1000000000000), orderedInterval (-34081241337 / 1000000000000) (-34081240831 / 1000000000000)))) (orderedInterval (-1524479331 / 1000000000000) (-1524479031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (147291528697593 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25832817178 / 1000000000000) (25832819059 / 1000000000000), orderedInterval (-52894518198 / 1000000000000) (-52894516317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (598731886774553 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29094524311 / 1000000000000) (29094525355 / 1000000000000), orderedInterval (2013444761 / 1000000000000) (2013445805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (399925152696727 / 800000000000) 4 (IntervalRat.scale (805 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32972938690 / 1000000000000) (-32972938688 / 1000000000000), orderedInterval (-13614830245 / 1000000000000) (-13614830243 / 1000000000000)))) (orderedInterval (-13563814837 / 1000000000000) (-13563813245 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate531_chunkChecks4 :
    compactCertificate531.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate531.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate531_chunkChecks4_0
    compactCertificate531_chunkChecks4_1 compactCertificate531_chunkChecks4_2

theorem compactCertificate531_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate531.chunkCheck r b = true :=
  compactCertificate531.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate531_chunkChecks0
    · exact compactCertificate531_chunkChecks1
    · exact compactCertificate531_chunkChecks2
    · exact compactCertificate531_chunkChecks3
    · exact compactCertificate531_chunkChecks4)

theorem compactCertificate531_coefficient0 :
    compactCertificate531.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate531_coefficient1 :
    compactCertificate531.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate531_coefficient2 :
    compactCertificate531.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate531_coefficient3 :
    compactCertificate531.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate531_coefficient4 :
    compactCertificate531.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate531_coefficients : ∀ r : Fin 5,
    compactCertificate531.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate531_coefficient0
  · exact compactCertificate531_coefficient1
  · exact compactCertificate531_coefficient2
  · exact compactCertificate531_coefficient3
  · exact compactCertificate531_coefficient4

theorem compactCertificate531_lower : (1 : ℚ) ≤ compactCertificate531.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate531, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate531_proves {t : ℝ} (ht : t ∈ compactCertificate531.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate531.proves compactCertificate531_states compactCertificate531_chunks
    compactCertificate531_coefficients compactCertificate531_lower ht

end Erdos232
