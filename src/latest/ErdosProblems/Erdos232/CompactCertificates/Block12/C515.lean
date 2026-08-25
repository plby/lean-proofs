/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate515 : CompactCertificate where
  left := 386
  right := 387
  center := 773 / 2
  grid := fun i =>
    match i.val with
    | 0 => 123
    | 1 => 91
    | 2 => 147
    | 3 => 26
    | 4 => 71
    | 5 => 193
    | 6 => 142
    | 7 => 244
    | 8 => 179
    | 9 => 275
    | 10 => 159
    | 11 => 282
    | 12 => 263
    | 13 => 188
    | 14 => 213
    | 15 => 178
    | 16 => 157
    | 17 => 228
    | 18 => 126
    | 19 => 107
    | 20 => 67
    | 21 => 36
    | 22 => 98
    | 23 => 133
    | 24 => 56
    | 25 => 229
    | _ => 153
  point := fun i =>
    match i.val with
    | 0 => 773 / 2
    | 1 => 1138776602727473 / 4000000000000
    | 2 => 368256955680209 / 800000000000
    | 3 => 332292172526611 / 4000000000000
    | 4 => 892583516166967 / 4000000000000
    | 5 => 2423537878614939 / 4000000000000
    | 6 => 1785167032334707 / 4000000000000
    | 7 => 3058914137102911 / 4000000000000
    | 8 => 2253182308591549 / 4000000000000
    | 9 => 3456961093214227 / 4000000000000
    | 10 => 1995877417745083 / 4000000000000
    | 11 => 3541719502091447 / 4000000000000
    | 12 => 3309133778624243 / 4000000000000
    | 13 => 2361554008133219 / 4000000000000
    | 14 => 2677750548500901 / 4000000000000
    | 15 => 2232429237811669 / 4000000000000
    | 16 => 1972418934393049 / 4000000000000
    | 17 => 571683885907851 / 800000000000
    | 18 => 1581307714495697 / 4000000000000
    | 19 => 1340492062081417 / 4000000000000
    | 20 => 838817691408451 / 4000000000000
    | 21 => 451118944221117 / 4000000000000
    | 22 => 1224875688694351 / 4000000000000
    | 23 => 1672463035068527 / 4000000000000
    | 24 => 707182308591549 / 4000000000000
    | 25 => 2874656822836829 / 4000000000000
    | _ => 1920137534376211 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))
    | 1 => (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))
    | 2 => (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000))
    | 3 => (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))
    | 4 => (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))
    | 5 => (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000))
    | 6 => (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))
    | 7 => (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))
    | 8 => (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000))
    | 9 => (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))
    | 10 => (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))
    | 11 => (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000))
    | 12 => (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))
    | 13 => (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))
    | 14 => (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000))
    | 15 => (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))
    | 16 => (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))
    | 17 => (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000))
    | 18 => (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))
    | 19 => (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))
    | 20 => (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000))
    | 21 => (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))
    | 22 => (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))
    | 23 => (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000))
    | 24 => (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))
    | 25 => (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))
    | _ => (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-10694038879 / 1000000000000) (-10694038471 / 1000000000000)
      | 1 => orderedInterval (-1508038778 / 1000000000000) (-1508038356 / 1000000000000)
      | 2 => orderedInterval (-36317372 / 1000000000000) (-36316179 / 1000000000000)
      | 3 => orderedInterval (4713394625 / 1000000000000) (4713394780 / 1000000000000)
      | 4 => orderedInterval (2254849231 / 1000000000000) (2254850097 / 1000000000000)
      | 5 => orderedInterval (545767702 / 1000000000000) (545768029 / 1000000000000)
      | 6 => orderedInterval (-2316302053 / 1000000000000) (-2316301953 / 1000000000000)
      | 7 => orderedInterval (2789747739 / 1000000000000) (2789749217 / 1000000000000)
      | _ => orderedInterval (1480997032 / 1000000000000) (1480997141 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12642222190 / 1000000000000) (-12642221708 / 1000000000000)
      | 1 => orderedInterval (2801387326 / 1000000000000) (2801387460 / 1000000000000)
      | 2 => orderedInterval (-704795975 / 1000000000000) (-704793683 / 1000000000000)
      | 3 => orderedInterval (10064613405 / 1000000000000) (10064613726 / 1000000000000)
      | 4 => orderedInterval (3886958383 / 1000000000000) (3886960211 / 1000000000000)
      | 5 => orderedInterval (3494148897 / 1000000000000) (3494149487 / 1000000000000)
      | 6 => orderedInterval (-5216564281 / 1000000000000) (-5216564188 / 1000000000000)
      | 7 => orderedInterval (663735768 / 1000000000000) (663736945 / 1000000000000)
      | _ => orderedInterval (12871866683 / 1000000000000) (12871866834 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10212566819 / 1000000000000) (10212567391 / 1000000000000)
      | 1 => orderedInterval (-1371740750 / 1000000000000) (-1371740659 / 1000000000000)
      | 2 => orderedInterval (-1291231766 / 1000000000000) (-1291227325 / 1000000000000)
      | 3 => orderedInterval (-25967731704 / 1000000000000) (-25967731016 / 1000000000000)
      | 4 => orderedInterval (-6450648259 / 1000000000000) (-6450644378 / 1000000000000)
      | 5 => orderedInterval (223253001 / 1000000000000) (223254073 / 1000000000000)
      | 6 => orderedInterval (2259113713 / 1000000000000) (2259113801 / 1000000000000)
      | 7 => orderedInterval (-3514119591 / 1000000000000) (-3514118648 / 1000000000000)
      | _ => orderedInterval (-1951713439 / 1000000000000) (-1951713216 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (13306370533 / 1000000000000) (13306371212 / 1000000000000)
      | 1 => orderedInterval (-8122398288 / 1000000000000) (-8122398175 / 1000000000000)
      | 2 => orderedInterval (3112386376 / 1000000000000) (3112395017 / 1000000000000)
      | 3 => orderedInterval (-63390857716 / 1000000000000) (-63390856207 / 1000000000000)
      | 4 => orderedInterval (-8521583257 / 1000000000000) (-8521575007 / 1000000000000)
      | 5 => orderedInterval (-7521343305 / 1000000000000) (-7521341348 / 1000000000000)
      | 6 => orderedInterval (5331505016 / 1000000000000) (5331505101 / 1000000000000)
      | 7 => orderedInterval (-1445657795 / 1000000000000) (-1445657038 / 1000000000000)
      | _ => orderedInterval (-28492464128 / 1000000000000) (-28492463785 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9449594692 / 1000000000000) (-9449593883 / 1000000000000)
      | 1 => orderedInterval (4544349693 / 1000000000000) (4544349862 / 1000000000000)
      | 2 => orderedInterval (8094550458 / 1000000000000) (8094567364 / 1000000000000)
      | 3 => orderedInterval (134950062806 / 1000000000000) (134950066152 / 1000000000000)
      | 4 => orderedInterval (20331126867 / 1000000000000) (20331144461 / 1000000000000)
      | 5 => orderedInterval (-4097317835 / 1000000000000) (-4097314246 / 1000000000000)
      | 6 => orderedInterval (-2244893599 / 1000000000000) (-2244893515 / 1000000000000)
      | 7 => orderedInterval (3905893967 / 1000000000000) (3905894580 / 1000000000000)
      | _ => orderedInterval (3402455393 / 1000000000000) (3402455944 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2769940753 / 1000000000000) (-2769935695 / 1000000000000)
    | 1 => orderedInterval (15219128016 / 1000000000000) (15219135084 / 1000000000000)
    | 2 => orderedInterval (-27852251976 / 1000000000000) (-27852239977 / 1000000000000)
    | 3 => orderedInterval (-95744042564 / 1000000000000) (-95744020230 / 1000000000000)
    | _ => orderedInterval (159436633058 / 1000000000000) (159436676719 / 1000000000000)

theorem compactCertificate515_stateChecks0 :
    compactCertificate515.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (773 / 2)) (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1138776602727473 / 4000000000000)) (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (368256955680209 / 800000000000)) (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks1 :
    compactCertificate515.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (332292172526611 / 4000000000000)) (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (892583516166967 / 4000000000000)) (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2423537878614939 / 4000000000000)) (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks2 :
    compactCertificate515.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1785167032334707 / 4000000000000)) (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3058914137102911 / 4000000000000)) (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2253182308591549 / 4000000000000)) (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks3 :
    compactCertificate515.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3456961093214227 / 4000000000000)) (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1995877417745083 / 4000000000000)) (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (3541719502091447 / 4000000000000)) (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks4 :
    compactCertificate515.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3309133778624243 / 4000000000000)) (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2361554008133219 / 4000000000000)) (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2677750548500901 / 4000000000000)) (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks5 :
    compactCertificate515.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2232429237811669 / 4000000000000)) (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1972418934393049 / 4000000000000)) (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (571683885907851 / 800000000000)) (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks6 :
    compactCertificate515.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1581307714495697 / 4000000000000)) (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1340492062081417 / 4000000000000)) (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (838817691408451 / 4000000000000)) (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks7 :
    compactCertificate515.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (451118944221117 / 4000000000000)) (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1224875688694351 / 4000000000000)) (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1672463035068527 / 4000000000000)) (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_stateChecks8 :
    compactCertificate515.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (707182308591549 / 4000000000000)) (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2874656822836829 / 4000000000000)) (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1920137534376211 / 4000000000000)) (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_states : ∀ j,
    BesselStateValid (compactCertificate515.point j) (compactCertificate515.state j) :=
  compactCertificate515.statesValid_of_checks3 compactCertificate515_stateChecks0
    compactCertificate515_stateChecks1 compactCertificate515_stateChecks2
    compactCertificate515_stateChecks3 compactCertificate515_stateChecks4
    compactCertificate515_stateChecks5 compactCertificate515_stateChecks6
    compactCertificate515_stateChecks7 compactCertificate515_stateChecks8

theorem compactCertificate515_chunkChecks0_0 :
    compactCertificate515.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (773 / 2) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1138776602727473 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (368256955680209 / 800000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000)))) (orderedInterval (-10694038879 / 1000000000000) (-10694038471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (332292172526611 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (892583516166967 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2423537878614939 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000)))) (orderedInterval (-1508038778 / 1000000000000) (-1508038356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1785167032334707 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3058914137102911 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2253182308591549 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000)))) (orderedInterval (-36317372 / 1000000000000) (-36316179 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks0_1 :
    compactCertificate515.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3456961093214227 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1995877417745083 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3541719502091447 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000)))) (orderedInterval (4713394625 / 1000000000000) (4713394780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3309133778624243 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2361554008133219 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2677750548500901 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000)))) (orderedInterval (2254849231 / 1000000000000) (2254850097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2232429237811669 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1972418934393049 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (571683885907851 / 800000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000)))) (orderedInterval (545767702 / 1000000000000) (545768029 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks0_2 :
    compactCertificate515.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1581307714495697 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1340492062081417 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (838817691408451 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000)))) (orderedInterval (-2316302053 / 1000000000000) (-2316301953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (451118944221117 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1224875688694351 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1672463035068527 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000)))) (orderedInterval (2789747739 / 1000000000000) (2789749217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (707182308591549 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2874656822836829 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1920137534376211 / 4000000000000) 0 (IntervalRat.scale (773 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000)))) (orderedInterval (1480997032 / 1000000000000) (1480997141 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks0 :
    compactCertificate515.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate515.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate515_chunkChecks0_0
    compactCertificate515_chunkChecks0_1 compactCertificate515_chunkChecks0_2

theorem compactCertificate515_chunkChecks1_0 :
    compactCertificate515.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (773 / 2) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1138776602727473 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (368256955680209 / 800000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000)))) (orderedInterval (-12642222190 / 1000000000000) (-12642221708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (332292172526611 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (892583516166967 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2423537878614939 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000)))) (orderedInterval (2801387326 / 1000000000000) (2801387460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1785167032334707 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3058914137102911 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2253182308591549 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000)))) (orderedInterval (-704795975 / 1000000000000) (-704793683 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks1_1 :
    compactCertificate515.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3456961093214227 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1995877417745083 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3541719502091447 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000)))) (orderedInterval (10064613405 / 1000000000000) (10064613726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3309133778624243 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2361554008133219 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2677750548500901 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000)))) (orderedInterval (3886958383 / 1000000000000) (3886960211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2232429237811669 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1972418934393049 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (571683885907851 / 800000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000)))) (orderedInterval (3494148897 / 1000000000000) (3494149487 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks1_2 :
    compactCertificate515.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1581307714495697 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1340492062081417 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (838817691408451 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000)))) (orderedInterval (-5216564281 / 1000000000000) (-5216564188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (451118944221117 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1224875688694351 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1672463035068527 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000)))) (orderedInterval (663735768 / 1000000000000) (663736945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (707182308591549 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2874656822836829 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1920137534376211 / 4000000000000) 1 (IntervalRat.scale (773 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000)))) (orderedInterval (12871866683 / 1000000000000) (12871866834 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks1 :
    compactCertificate515.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate515.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate515_chunkChecks1_0
    compactCertificate515_chunkChecks1_1 compactCertificate515_chunkChecks1_2

theorem compactCertificate515_chunkChecks2_0 :
    compactCertificate515.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (773 / 2) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1138776602727473 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (368256955680209 / 800000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000)))) (orderedInterval (10212566819 / 1000000000000) (10212567391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (332292172526611 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (892583516166967 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2423537878614939 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000)))) (orderedInterval (-1371740750 / 1000000000000) (-1371740659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1785167032334707 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3058914137102911 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2253182308591549 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000)))) (orderedInterval (-1291231766 / 1000000000000) (-1291227325 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks2_1 :
    compactCertificate515.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3456961093214227 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1995877417745083 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3541719502091447 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000)))) (orderedInterval (-25967731704 / 1000000000000) (-25967731016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3309133778624243 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2361554008133219 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2677750548500901 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000)))) (orderedInterval (-6450648259 / 1000000000000) (-6450644378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2232429237811669 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1972418934393049 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (571683885907851 / 800000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000)))) (orderedInterval (223253001 / 1000000000000) (223254073 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks2_2 :
    compactCertificate515.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1581307714495697 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1340492062081417 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (838817691408451 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000)))) (orderedInterval (2259113713 / 1000000000000) (2259113801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (451118944221117 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1224875688694351 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1672463035068527 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000)))) (orderedInterval (-3514119591 / 1000000000000) (-3514118648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (707182308591549 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2874656822836829 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1920137534376211 / 4000000000000) 2 (IntervalRat.scale (773 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000)))) (orderedInterval (-1951713439 / 1000000000000) (-1951713216 / 1000000000000))) = true
  rfl'

theorem compactCertificate515_chunkChecks2 :
    compactCertificate515.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate515.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate515_chunkChecks2_0
    compactCertificate515_chunkChecks2_1 compactCertificate515_chunkChecks2_2

theorem compactCertificate515_chunkChecks3_0 :
    compactCertificate515.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (773 / 2) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1138776602727473 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (368256955680209 / 800000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000)))) (orderedInterval (13306370533 / 1000000000000) (13306371212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (332292172526611 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (892583516166967 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2423537878614939 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000)))) (orderedInterval (-8122398288 / 1000000000000) (-8122398175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1785167032334707 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3058914137102911 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2253182308591549 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000)))) (orderedInterval (3112386376 / 1000000000000) (3112395017 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate515_chunkChecks3_1 :
    compactCertificate515.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3456961093214227 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1995877417745083 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3541719502091447 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000)))) (orderedInterval (-63390857716 / 1000000000000) (-63390856207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3309133778624243 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2361554008133219 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2677750548500901 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000)))) (orderedInterval (-8521583257 / 1000000000000) (-8521575007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2232429237811669 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1972418934393049 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (571683885907851 / 800000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000)))) (orderedInterval (-7521343305 / 1000000000000) (-7521341348 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate515_chunkChecks3_2 :
    compactCertificate515.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1581307714495697 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1340492062081417 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (838817691408451 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000)))) (orderedInterval (5331505016 / 1000000000000) (5331505101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (451118944221117 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1224875688694351 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1672463035068527 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000)))) (orderedInterval (-1445657795 / 1000000000000) (-1445657038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (707182308591549 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2874656822836829 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1920137534376211 / 4000000000000) 3 (IntervalRat.scale (773 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000)))) (orderedInterval (-28492464128 / 1000000000000) (-28492463785 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate515_chunkChecks3 :
    compactCertificate515.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate515.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate515_chunkChecks3_0
    compactCertificate515_chunkChecks3_1 compactCertificate515_chunkChecks3_2

theorem compactCertificate515_chunkChecks4_0 :
    compactCertificate515.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (773 / 2) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30998746875 / 1000000000000) (-30998746874 / 1000000000000), orderedInterval (-26155658968 / 1000000000000) (-26155658967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1138776602727473 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18668044390 / 1000000000000) (18668044966 / 1000000000000), orderedInterval (-43479993465 / 1000000000000) (-43479992888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (368256955680209 / 800000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24178624764 / 1000000000000) (24178631166 / 1000000000000), orderedInterval (-28281963122 / 1000000000000) (-28281956721 / 1000000000000)))) (orderedInterval (-9449594692 / 1000000000000) (-9449593883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (332292172526611 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72015108442 / 1000000000000) (72015142967 / 1000000000000), orderedInterval (-50204381895 / 1000000000000) (-50204347370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (892583516166967 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41086819844 / 1000000000000) (-41086819843 / 1000000000000), orderedInterval (-34037145444 / 1000000000000) (-34037145443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2423537878614939 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10879588183 / 1000000000000) (-10879588182 / 1000000000000), orderedInterval (-30525638657 / 1000000000000) (-30525638656 / 1000000000000)))) (orderedInterval (4544349693 / 1000000000000) (4544349862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1785167032334707 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31170100733 / 1000000000000) (31170100734 / 1000000000000), orderedInterval (21293227914 / 1000000000000) (21293227915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3058914137102911 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24806982543 / 1000000000000) (-24806948509 / 1000000000000), orderedInterval (14750260553 / 1000000000000) (14750294588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2253182308591549 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33162115615 / 1000000000000) (-33162110590 / 1000000000000), orderedInterval (5547027473 / 1000000000000) (5547032498 / 1000000000000)))) (orderedInterval (8094550458 / 1000000000000) (8094567364 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate515_chunkChecks4_1 :
    compactCertificate515.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3456961093214227 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24032909185 / 1000000000000) (-24032909178 / 1000000000000), orderedInterval (-12597313004 / 1000000000000) (-12597312996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1995877417745083 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8534635027 / 1000000000000) (-8534635026 / 1000000000000), orderedInterval (-34676171408 / 1000000000000) (-34676171407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3541719502091447 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7564815800 / 1000000000000) (7564815801 / 1000000000000), orderedInterval (25720595373 / 1000000000000) (25720595374 / 1000000000000)))) (orderedInterval (134950062806 / 1000000000000) (134950066152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3309133778624243 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26814997783 / 1000000000000) (-26814952425 / 1000000000000), orderedInterval (7121630390 / 1000000000000) (7121675747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2361554008133219 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17283149381 / 1000000000000) (17283149382 / 1000000000000), orderedInterval (27906670941 / 1000000000000) (27906670942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2677750548500901 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26955918332 / 1000000000000) (-26955918330 / 1000000000000), orderedInterval (-14958361065 / 1000000000000) (-14958361064 / 1000000000000)))) (orderedInterval (20331126867 / 1000000000000) (20331144461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2232429237811669 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10335456046 / 1000000000000) (-10335456023 / 1000000000000), orderedInterval (32162875108 / 1000000000000) (32162875131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1972418934393049 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22025176471 / 1000000000000) (-22025176470 / 1000000000000), orderedInterval (-28366669871 / 1000000000000) (-28366669870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (571683885907851 / 800000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23250689969 / 1000000000000) (-23250678660 / 1000000000000), orderedInterval (18731904757 / 1000000000000) (18731916067 / 1000000000000)))) (orderedInterval (-4097317835 / 1000000000000) (-4097314246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate515_chunkChecks4_2 :
    compactCertificate515.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1581307714495697 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10755418624 / 1000000000000) (10755418625 / 1000000000000), orderedInterval (38647551163 / 1000000000000) (38647551164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1340492062081417 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (10460728325 / 1000000000000) (10460728370 / 1000000000000), orderedInterval (-42326775874 / 1000000000000) (-42326775830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (838817691408451 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-138690001 / 1000000000000) (-138689998 / 1000000000000), orderedInterval (-55097627841 / 1000000000000) (-55097627838 / 1000000000000)))) (orderedInterval (-2244893599 / 1000000000000) (-2244893515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (451118944221117 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33804171316 / 1000000000000) (33804171317 / 1000000000000), orderedInterval (66947954331 / 1000000000000) (66947954332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1224875688694351 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34913790686 / 1000000000000) (-34913727591 / 1000000000000), orderedInterval (29382702509 / 1000000000000) (29382765605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1672463035068527 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34210614291 / 1000000000000) (-34210614289 / 1000000000000), orderedInterval (-18726759557 / 1000000000000) (-18726759556 / 1000000000000)))) (orderedInterval (3905893967 / 1000000000000) (3905894580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (707182308591549 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59813936237 / 1000000000000) (59813936416 / 1000000000000), orderedInterval (-4981587063 / 1000000000000) (-4981586884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2874656822836829 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-735436844 / 1000000000000) (-735436843 / 1000000000000), orderedInterval (-29753428287 / 1000000000000) (-29753428286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1920137534376211 / 4000000000000) 4 (IntervalRat.scale (773 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5652469351 / 1000000000000) (-5652469350 / 1000000000000), orderedInterval (-35969749594 / 1000000000000) (-35969749593 / 1000000000000)))) (orderedInterval (3402455393 / 1000000000000) (3402455944 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate515_chunkChecks4 :
    compactCertificate515.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate515.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate515_chunkChecks4_0
    compactCertificate515_chunkChecks4_1 compactCertificate515_chunkChecks4_2

theorem compactCertificate515_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate515.chunkCheck r b = true :=
  compactCertificate515.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate515_chunkChecks0
    · exact compactCertificate515_chunkChecks1
    · exact compactCertificate515_chunkChecks2
    · exact compactCertificate515_chunkChecks3
    · exact compactCertificate515_chunkChecks4)

theorem compactCertificate515_coefficient0 :
    compactCertificate515.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate515_coefficient1 :
    compactCertificate515.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate515_coefficient2 :
    compactCertificate515.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate515_coefficient3 :
    compactCertificate515.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate515_coefficient4 :
    compactCertificate515.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate515_coefficients : ∀ r : Fin 5,
    compactCertificate515.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate515_coefficient0
  · exact compactCertificate515_coefficient1
  · exact compactCertificate515_coefficient2
  · exact compactCertificate515_coefficient3
  · exact compactCertificate515_coefficient4

theorem compactCertificate515_lower : (1 : ℚ) ≤ compactCertificate515.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate515, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate515_proves {t : ℝ} (ht : t ∈ compactCertificate515.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate515.proves compactCertificate515_states compactCertificate515_chunks
    compactCertificate515_coefficients compactCertificate515_lower ht

end Erdos232
