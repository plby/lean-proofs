/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate409 : CompactCertificate where
  left := 280
  right := 281
  center := 561 / 2
  grid := fun i =>
    match i.val with
    | 0 => 89
    | 1 => 66
    | 2 => 106
    | 3 => 19
    | 4 => 52
    | 5 => 140
    | 6 => 103
    | 7 => 177
    | 8 => 130
    | 9 => 200
    | 10 => 115
    | 11 => 205
    | 12 => 191
    | 13 => 136
    | 14 => 155
    | 15 => 129
    | 16 => 114
    | 17 => 165
    | 18 => 91
    | 19 => 77
    | 20 => 48
    | 21 => 26
    | 22 => 71
    | 23 => 97
    | 24 => 41
    | 25 => 166
    | _ => 111
  point := fun i =>
    match i.val with
    | 0 => 561 / 2
    | 1 => 826460121772461 / 4000000000000
    | 2 => 267260222686413 / 800000000000
    | 3 => 241159002312327 / 4000000000000
    | 4 => 647787002030619 / 4000000000000
    | 5 => 1758867723031023 / 4000000000000
    | 6 => 1295574004061799 / 4000000000000
    | 7 => 2219988138311427 / 4000000000000
    | 8 => 1635233214902793 / 4000000000000
    | 9 => 2508868270754439 / 4000000000000
    | 10 => 1448495771481231 / 4000000000000
    | 11 => 2570381165165979 / 4000000000000
    | 12 => 2401583505573351 / 4000000000000
    | 13 => 1713883309912983 / 4000000000000
    | 14 => 1943361006091857 / 4000000000000
    | 15 => 1620171801309633 / 4000000000000
    | 16 => 1431470921338293 / 4000000000000
    | 17 => 414896067263007 / 800000000000
    | 18 => 1147624356833229 / 4000000000000
    | 19 => 972853876879269 / 4000000000000
    | 20 => 608766785097207 / 4000000000000
    | 21 => 327396801692169 / 4000000000000
    | 22 => 888946004343507 / 4000000000000
    | 23 => 1213779770599539 / 4000000000000
    | 24 => 513233214902793 / 4000000000000
    | 25 => 2086264524723753 / 4000000000000
    | _ => 1393528016539527 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))
    | 1 => (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))
    | 2 => (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000))
    | 3 => (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))
    | 4 => (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
    | 5 => (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000))
    | 6 => (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))
    | 7 => (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))
    | 8 => (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000))
    | 9 => (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))
    | 10 => (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))
    | 11 => (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000))
    | 12 => (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))
    | 13 => (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))
    | 14 => (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000))
    | 15 => (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))
    | 16 => (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))
    | 17 => (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000))
    | 18 => (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))
    | 19 => (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))
    | 20 => (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000))
    | 21 => (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))
    | 22 => (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))
    | 23 => (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000))
    | 24 => (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))
    | 25 => (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))
    | _ => (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16274053677 / 1000000000000) (-16274053150 / 1000000000000)
      | 1 => orderedInterval (-1955045784 / 1000000000000) (-1955045256 / 1000000000000)
      | 2 => orderedInterval (595723262 / 1000000000000) (595723279 / 1000000000000)
      | 3 => orderedInterval (1352372465 / 1000000000000) (1352372778 / 1000000000000)
      | 4 => orderedInterval (3790913474 / 1000000000000) (3790916709 / 1000000000000)
      | 5 => orderedInterval (-2199784607 / 1000000000000) (-2199784580 / 1000000000000)
      | 6 => orderedInterval (11557051333 / 1000000000000) (11557055333 / 1000000000000)
      | 7 => orderedInterval (-3061705834 / 1000000000000) (-3061705672 / 1000000000000)
      | _ => orderedInterval (1239394264 / 1000000000000) (1239394343 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1682450737 / 1000000000000) (1682451322 / 1000000000000)
      | 1 => orderedInterval (-2184541640 / 1000000000000) (-2184541316 / 1000000000000)
      | 2 => orderedInterval (2506841656 / 1000000000000) (2506841685 / 1000000000000)
      | 3 => orderedInterval (-19997159633 / 1000000000000) (-19997158973 / 1000000000000)
      | 4 => orderedInterval (-1490369362 / 1000000000000) (-1490364419 / 1000000000000)
      | 5 => orderedInterval (-4077074546 / 1000000000000) (-4077074507 / 1000000000000)
      | 6 => orderedInterval (-3728644629 / 1000000000000) (-3728641613 / 1000000000000)
      | 7 => orderedInterval (4015512839 / 1000000000000) (4015513009 / 1000000000000)
      | _ => orderedInterval (5278012773 / 1000000000000) (5278012883 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15250955414 / 1000000000000) (15250956071 / 1000000000000)
      | 1 => orderedInterval (4582574241 / 1000000000000) (4582574460 / 1000000000000)
      | 2 => orderedInterval (-757885656 / 1000000000000) (-757885605 / 1000000000000)
      | 3 => orderedInterval (-17698637278 / 1000000000000) (-17698635840 / 1000000000000)
      | 4 => orderedInterval (-10000703167 / 1000000000000) (-10000695592 / 1000000000000)
      | 5 => orderedInterval (5094238408 / 1000000000000) (5094238467 / 1000000000000)
      | 6 => orderedInterval (-10041615762 / 1000000000000) (-10041613350 / 1000000000000)
      | 7 => orderedInterval (2108745073 / 1000000000000) (2108745254 / 1000000000000)
      | _ => orderedInterval (1988955815 / 1000000000000) (1988955977 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1207298918 / 1000000000000) (-1207298177 / 1000000000000)
      | 1 => orderedInterval (7726423878 / 1000000000000) (7726424054 / 1000000000000)
      | 2 => orderedInterval (-8880476277 / 1000000000000) (-8880476185 / 1000000000000)
      | 3 => orderedInterval (102835150632 / 1000000000000) (102835153823 / 1000000000000)
      | 4 => orderedInterval (2125176814 / 1000000000000) (2125188399 / 1000000000000)
      | 5 => orderedInterval (8368488604 / 1000000000000) (8368488694 / 1000000000000)
      | 6 => orderedInterval (3071252946 / 1000000000000) (3071254953 / 1000000000000)
      | 7 => orderedInterval (-4481724990 / 1000000000000) (-4481724796 / 1000000000000)
      | _ => orderedInterval (-1697716156 / 1000000000000) (-1697715906 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13794085807 / 1000000000000) (-13794084963 / 1000000000000)
      | 1 => orderedInterval (-10462443140 / 1000000000000) (-10462442962 / 1000000000000)
      | 2 => orderedInterval (-367576645 / 1000000000000) (-367576474 / 1000000000000)
      | 3 => orderedInterval (108857251846 / 1000000000000) (108857259010 / 1000000000000)
      | 4 => orderedInterval (28710156287 / 1000000000000) (28710174057 / 1000000000000)
      | 5 => orderedInterval (-13303552472 / 1000000000000) (-13303552330 / 1000000000000)
      | 6 => orderedInterval (9560568868 / 1000000000000) (9560570603 / 1000000000000)
      | 7 => orderedInterval (-2316958760 / 1000000000000) (-2316958551 / 1000000000000)
      | _ => orderedInterval (-17158175707 / 1000000000000) (-17158175306 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-4955135104 / 1000000000000) (-4955126216 / 1000000000000)
    | 1 => orderedInterval (-17994971805 / 1000000000000) (-17994961929 / 1000000000000)
    | 2 => orderedInterval (-9473372912 / 1000000000000) (-9473360158 / 1000000000000)
    | 3 => orderedInterval (107859276533 / 1000000000000) (107859294859 / 1000000000000)
    | _ => orderedInterval (89725184470 / 1000000000000) (89725213084 / 1000000000000)

theorem compactCertificate409_stateChecks0 :
    compactCertificate409.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (561 / 2)) (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (826460121772461 / 4000000000000)) (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (267260222686413 / 800000000000)) (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks1 :
    compactCertificate409.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (241159002312327 / 4000000000000)) (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (647787002030619 / 4000000000000)) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1758867723031023 / 4000000000000)) (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks2 :
    compactCertificate409.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1295574004061799 / 4000000000000)) (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2219988138311427 / 4000000000000)) (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1635233214902793 / 4000000000000)) (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks3 :
    compactCertificate409.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2508868270754439 / 4000000000000)) (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1448495771481231 / 4000000000000)) (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2570381165165979 / 4000000000000)) (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks4 :
    compactCertificate409.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2401583505573351 / 4000000000000)) (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1713883309912983 / 4000000000000)) (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1943361006091857 / 4000000000000)) (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks5 :
    compactCertificate409.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1620171801309633 / 4000000000000)) (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1431470921338293 / 4000000000000)) (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (414896067263007 / 800000000000)) (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks6 :
    compactCertificate409.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1147624356833229 / 4000000000000)) (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (972853876879269 / 4000000000000)) (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (608766785097207 / 4000000000000)) (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks7 :
    compactCertificate409.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (327396801692169 / 4000000000000)) (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (888946004343507 / 4000000000000)) (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1213779770599539 / 4000000000000)) (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_stateChecks8 :
    compactCertificate409.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (513233214902793 / 4000000000000)) (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2086264524723753 / 4000000000000)) (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1393528016539527 / 4000000000000)) (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_states : ∀ j,
    BesselStateValid (compactCertificate409.point j) (compactCertificate409.state j) :=
  compactCertificate409.statesValid_of_checks3 compactCertificate409_stateChecks0
    compactCertificate409_stateChecks1 compactCertificate409_stateChecks2
    compactCertificate409_stateChecks3 compactCertificate409_stateChecks4
    compactCertificate409_stateChecks5 compactCertificate409_stateChecks6
    compactCertificate409_stateChecks7 compactCertificate409_stateChecks8

theorem compactCertificate409_chunkChecks0_0 :
    compactCertificate409.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (561 / 2) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (826460121772461 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (267260222686413 / 800000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000)))) (orderedInterval (-16274053677 / 1000000000000) (-16274053150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (241159002312327 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1758867723031023 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000)))) (orderedInterval (-1955045784 / 1000000000000) (-1955045256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1295574004061799 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2219988138311427 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1635233214902793 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000)))) (orderedInterval (595723262 / 1000000000000) (595723279 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks0_1 :
    compactCertificate409.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2508868270754439 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1448495771481231 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2570381165165979 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000)))) (orderedInterval (1352372465 / 1000000000000) (1352372778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2401583505573351 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1713883309912983 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1943361006091857 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000)))) (orderedInterval (3790913474 / 1000000000000) (3790916709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1620171801309633 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1431470921338293 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (414896067263007 / 800000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000)))) (orderedInterval (-2199784607 / 1000000000000) (-2199784580 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks0_2 :
    compactCertificate409.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1147624356833229 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (972853876879269 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (608766785097207 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000)))) (orderedInterval (11557051333 / 1000000000000) (11557055333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (327396801692169 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (888946004343507 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1213779770599539 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000)))) (orderedInterval (-3061705834 / 1000000000000) (-3061705672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (513233214902793 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2086264524723753 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1393528016539527 / 4000000000000) 0 (IntervalRat.scale (561 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000)))) (orderedInterval (1239394264 / 1000000000000) (1239394343 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks0 :
    compactCertificate409.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate409.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate409_chunkChecks0_0
    compactCertificate409_chunkChecks0_1 compactCertificate409_chunkChecks0_2

theorem compactCertificate409_chunkChecks1_0 :
    compactCertificate409.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (561 / 2) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (826460121772461 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (267260222686413 / 800000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000)))) (orderedInterval (1682450737 / 1000000000000) (1682451322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (241159002312327 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1758867723031023 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000)))) (orderedInterval (-2184541640 / 1000000000000) (-2184541316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1295574004061799 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2219988138311427 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1635233214902793 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000)))) (orderedInterval (2506841656 / 1000000000000) (2506841685 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks1_1 :
    compactCertificate409.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2508868270754439 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1448495771481231 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2570381165165979 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000)))) (orderedInterval (-19997159633 / 1000000000000) (-19997158973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2401583505573351 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1713883309912983 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1943361006091857 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000)))) (orderedInterval (-1490369362 / 1000000000000) (-1490364419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1620171801309633 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1431470921338293 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (414896067263007 / 800000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000)))) (orderedInterval (-4077074546 / 1000000000000) (-4077074507 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks1_2 :
    compactCertificate409.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1147624356833229 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (972853876879269 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (608766785097207 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000)))) (orderedInterval (-3728644629 / 1000000000000) (-3728641613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (327396801692169 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (888946004343507 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1213779770599539 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000)))) (orderedInterval (4015512839 / 1000000000000) (4015513009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (513233214902793 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2086264524723753 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1393528016539527 / 4000000000000) 1 (IntervalRat.scale (561 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000)))) (orderedInterval (5278012773 / 1000000000000) (5278012883 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks1 :
    compactCertificate409.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate409.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate409_chunkChecks1_0
    compactCertificate409_chunkChecks1_1 compactCertificate409_chunkChecks1_2

theorem compactCertificate409_chunkChecks2_0 :
    compactCertificate409.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (561 / 2) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (826460121772461 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (267260222686413 / 800000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000)))) (orderedInterval (15250955414 / 1000000000000) (15250956071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (241159002312327 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1758867723031023 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000)))) (orderedInterval (4582574241 / 1000000000000) (4582574460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1295574004061799 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2219988138311427 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1635233214902793 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000)))) (orderedInterval (-757885656 / 1000000000000) (-757885605 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks2_1 :
    compactCertificate409.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2508868270754439 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1448495771481231 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2570381165165979 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000)))) (orderedInterval (-17698637278 / 1000000000000) (-17698635840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2401583505573351 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1713883309912983 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1943361006091857 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000)))) (orderedInterval (-10000703167 / 1000000000000) (-10000695592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1620171801309633 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1431470921338293 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (414896067263007 / 800000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000)))) (orderedInterval (5094238408 / 1000000000000) (5094238467 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks2_2 :
    compactCertificate409.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1147624356833229 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (972853876879269 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (608766785097207 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000)))) (orderedInterval (-10041615762 / 1000000000000) (-10041613350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (327396801692169 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (888946004343507 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1213779770599539 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000)))) (orderedInterval (2108745073 / 1000000000000) (2108745254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (513233214902793 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2086264524723753 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1393528016539527 / 4000000000000) 2 (IntervalRat.scale (561 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000)))) (orderedInterval (1988955815 / 1000000000000) (1988955977 / 1000000000000))) = true
  rfl'

theorem compactCertificate409_chunkChecks2 :
    compactCertificate409.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate409.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate409_chunkChecks2_0
    compactCertificate409_chunkChecks2_1 compactCertificate409_chunkChecks2_2

theorem compactCertificate409_chunkChecks3_0 :
    compactCertificate409.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (561 / 2) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (826460121772461 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (267260222686413 / 800000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000)))) (orderedInterval (-1207298918 / 1000000000000) (-1207298177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (241159002312327 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1758867723031023 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000)))) (orderedInterval (7726423878 / 1000000000000) (7726424054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1295574004061799 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2219988138311427 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1635233214902793 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000)))) (orderedInterval (-8880476277 / 1000000000000) (-8880476185 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate409_chunkChecks3_1 :
    compactCertificate409.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2508868270754439 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1448495771481231 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2570381165165979 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000)))) (orderedInterval (102835150632 / 1000000000000) (102835153823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2401583505573351 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1713883309912983 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1943361006091857 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000)))) (orderedInterval (2125176814 / 1000000000000) (2125188399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1620171801309633 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1431470921338293 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (414896067263007 / 800000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000)))) (orderedInterval (8368488604 / 1000000000000) (8368488694 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate409_chunkChecks3_2 :
    compactCertificate409.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1147624356833229 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (972853876879269 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (608766785097207 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000)))) (orderedInterval (3071252946 / 1000000000000) (3071254953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (327396801692169 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (888946004343507 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1213779770599539 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000)))) (orderedInterval (-4481724990 / 1000000000000) (-4481724796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (513233214902793 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2086264524723753 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1393528016539527 / 4000000000000) 3 (IntervalRat.scale (561 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000)))) (orderedInterval (-1697716156 / 1000000000000) (-1697715906 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate409_chunkChecks3 :
    compactCertificate409.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate409.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate409_chunkChecks3_0
    compactCertificate409_chunkChecks3_1 compactCertificate409_chunkChecks3_2

theorem compactCertificate409_chunkChecks4_0 :
    compactCertificate409.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (561 / 2) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47339494028 / 1000000000000) (-47339493492 / 1000000000000), orderedInterval (5428354110 / 1000000000000) (5428354646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (826460121772461 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3035264282 / 1000000000000) (3035264284 / 1000000000000), orderedInterval (55418138450 / 1000000000000) (55418138452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (267260222686413 / 800000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41945023179 / 1000000000000) (41945028188 / 1000000000000), orderedInterval (-12155370107 / 1000000000000) (-12155365098 / 1000000000000)))) (orderedInterval (-13794085807 / 1000000000000) (-13794084963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (241159002312327 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100946654016 / 1000000000000) (-100946654014 / 1000000000000), orderedInterval (-18366317475 / 1000000000000) (-18366317473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1758867723031023 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23898068375 / 1000000000000) (23898068376 / 1000000000000), orderedInterval (29581558615 / 1000000000000) (29581558616 / 1000000000000)))) (orderedInterval (-10462443140 / 1000000000000) (-10462442962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1295574004061799 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39399135805 / 1000000000000) (-39399135804 / 1000000000000), orderedInterval (-20267205226 / 1000000000000) (-20267205225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2219988138311427 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (9349702694 / 1000000000000) (9349702709 / 1000000000000), orderedInterval (-32560723208 / 1000000000000) (-32560723194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1635233214902793 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36581617105 / 1000000000000) (36581617106 / 1000000000000), orderedInterval (14755322229 / 1000000000000) (14755322231 / 1000000000000)))) (orderedInterval (-367576645 / 1000000000000) (-367576474 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate409_chunkChecks4_1 :
    compactCertificate409.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2508868270754439 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9908703561 / 1000000000000) (-9908703547 / 1000000000000), orderedInterval (30286752991 / 1000000000000) (30286753006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1448495771481231 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41865181038 / 1000000000000) (-41865180600 / 1000000000000), orderedInterval (2364579203 / 1000000000000) (2364579641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2570381165165979 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18948078101 / 1000000000000) (18948079274 / 1000000000000), orderedInterval (-25147816933 / 1000000000000) (-25147815760 / 1000000000000)))) (orderedInterval (108857251846 / 1000000000000) (108857259010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2401583505573351 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29544896336 / 1000000000000) (-29544896333 / 1000000000000), orderedInterval (-13665984070 / 1000000000000) (-13665984068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1713883309912983 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35060449672 / 1000000000000) (35060483509 / 1000000000000), orderedInterval (-16058354501 / 1000000000000) (-16058320664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1943361006091857 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11437367381 / 1000000000000) (11437367427 / 1000000000000), orderedInterval (-34356131557 / 1000000000000) (-34356131511 / 1000000000000)))) (orderedInterval (28710156287 / 1000000000000) (28710174057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1620171801309633 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21145766723 / 1000000000000) (-21145766722 / 1000000000000), orderedInterval (-33508819850 / 1000000000000) (-33508819849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1431470921338293 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20634760397 / 1000000000000) (20634760398 / 1000000000000), orderedInterval (36756117173 / 1000000000000) (36756117174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (414896067263007 / 800000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30258670598 / 1000000000000) (-30258670597 / 1000000000000), orderedInterval (-17632617950 / 1000000000000) (-17632617949 / 1000000000000)))) (orderedInterval (-13303552472 / 1000000000000) (-13303552330 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate409_chunkChecks4_2 :
    compactCertificate409.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1147624356833229 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45807033987 / 1000000000000) (-45807031619 / 1000000000000), orderedInterval (11062822045 / 1000000000000) (11062824413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (972853876879269 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44273524613 / 1000000000000) (-44273489954 / 1000000000000), orderedInterval (25730593095 / 1000000000000) (25730627754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (608766785097207 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53047496953 / 1000000000000) (53047545751 / 1000000000000), orderedInterval (-37173828336 / 1000000000000) (-37173779539 / 1000000000000)))) (orderedInterval (9560568868 / 1000000000000) (9560570603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (327396801692169 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71821861220 / 1000000000000) (71821861221 / 1000000000000), orderedInterval (50742639686 / 1000000000000) (50742639687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (888946004343507 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1698587351 / 1000000000000) (1698587355 / 1000000000000), orderedInterval (-53498932990 / 1000000000000) (-53498932986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1213779770599539 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22142432449 / 1000000000000) (22142434117 / 1000000000000), orderedInterval (-40132479764 / 1000000000000) (-40132478096 / 1000000000000)))) (orderedInterval (-2316958760 / 1000000000000) (-2316958551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (513233214902793 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19968480530 / 1000000000000) (-19968480529 / 1000000000000), orderedInterval (-67471669696 / 1000000000000) (-67471669695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2086264524723753 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26176070348 / 1000000000000) (26176070349 / 1000000000000), orderedInterval (23113745852 / 1000000000000) (23113745853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1393528016539527 / 4000000000000) 4 (IntervalRat.scale (561 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18603709992 / 1000000000000) (-18603709991 / 1000000000000), orderedInterval (-38460497604 / 1000000000000) (-38460497603 / 1000000000000)))) (orderedInterval (-17158175707 / 1000000000000) (-17158175306 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate409_chunkChecks4 :
    compactCertificate409.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate409.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate409_chunkChecks4_0
    compactCertificate409_chunkChecks4_1 compactCertificate409_chunkChecks4_2

theorem compactCertificate409_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate409.chunkCheck r b = true :=
  compactCertificate409.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate409_chunkChecks0
    · exact compactCertificate409_chunkChecks1
    · exact compactCertificate409_chunkChecks2
    · exact compactCertificate409_chunkChecks3
    · exact compactCertificate409_chunkChecks4)

theorem compactCertificate409_coefficient0 :
    compactCertificate409.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate409_coefficient1 :
    compactCertificate409.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate409_coefficient2 :
    compactCertificate409.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate409_coefficient3 :
    compactCertificate409.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate409_coefficient4 :
    compactCertificate409.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate409_coefficients : ∀ r : Fin 5,
    compactCertificate409.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate409_coefficient0
  · exact compactCertificate409_coefficient1
  · exact compactCertificate409_coefficient2
  · exact compactCertificate409_coefficient3
  · exact compactCertificate409_coefficient4

theorem compactCertificate409_lower : (1 : ℚ) ≤ compactCertificate409.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate409, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate409_proves {t : ℝ} (ht : t ∈ compactCertificate409.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate409.proves compactCertificate409_states compactCertificate409_chunks
    compactCertificate409_coefficients compactCertificate409_lower ht

end Erdos232
