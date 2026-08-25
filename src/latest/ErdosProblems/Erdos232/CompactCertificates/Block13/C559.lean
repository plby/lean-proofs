/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate559 : CompactCertificate where
  left := 430
  right := 431
  center := 861 / 2
  grid := fun i =>
    match i.val with
    | 0 => 137
    | 1 => 101
    | 2 => 163
    | 3 => 29
    | 4 => 79
    | 5 => 215
    | 6 => 158
    | 7 => 271
    | 8 => 200
    | 9 => 307
    | 10 => 177
    | 11 => 314
    | 12 => 293
    | 13 => 209
    | 14 => 237
    | 15 => 198
    | 16 => 175
    | 17 => 253
    | 18 => 140
    | 19 => 119
    | 20 => 74
    | 21 => 40
    | 22 => 109
    | 23 => 148
    | 24 => 63
    | 25 => 255
    | _ => 170
  point := fun i =>
    match i.val with
    | 0 => 861 / 2
    | 1 => 1268417406142761 / 4000000000000
    | 2 => 410180127866313 / 800000000000
    | 3 => 370121035634427 / 4000000000000
    | 4 => 994197163544319 / 4000000000000
    | 5 => 2699438697913923 / 4000000000000
    | 6 => 1988394327089499 / 4000000000000
    | 7 => 3407147570563527 / 4000000000000
    | 8 => 2509689479556693 / 4000000000000
    | 9 => 3850509057254139 / 4000000000000
    | 10 => 2223092440722531 / 4000000000000
    | 11 => 3944916547607679 / 4000000000000
    | 12 => 3685852759890651 / 4000000000000
    | 13 => 2630398448903883 / 4000000000000
    | 14 => 2982591490632957 / 4000000000000
    | 15 => 2486573834095533 / 4000000000000
    | 16 => 2196963392642193 / 4000000000000
    | 17 => 636765621949107 / 800000000000
    | 18 => 1761327221449929 / 4000000000000
    | 19 => 1493096591787969 / 4000000000000
    | 20 => 934310520443307 / 4000000000000
    | 21 => 502475305270869 / 4000000000000
    | 22 => 1364318199179607 / 4000000000000
    | 23 => 1862859861829239 / 4000000000000
    | 24 => 787689479556693 / 4000000000000
    | 25 => 3201914003185653 / 4000000000000
    | _ => 2138730164421627 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))
    | 1 => (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))
    | 2 => (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000))
    | 3 => (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))
    | 4 => (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
    | 5 => (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000))
    | 6 => (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))
    | 7 => (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))
    | 8 => (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000))
    | 9 => (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))
    | 10 => (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))
    | 11 => (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000))
    | 12 => (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))
    | 13 => (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))
    | 14 => (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000))
    | 15 => (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))
    | 16 => (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))
    | 17 => (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000))
    | 18 => (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))
    | 19 => (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))
    | 20 => (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000))
    | 21 => (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))
    | 22 => (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))
    | 23 => (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000))
    | 24 => (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))
    | 25 => (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))
    | _ => (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14093899032 / 1000000000000) (-14093898996 / 1000000000000)
      | 1 => orderedInterval (-523108891 / 1000000000000) (-523108316 / 1000000000000)
      | 2 => orderedInterval (700837349 / 1000000000000) (700837375 / 1000000000000)
      | 3 => orderedInterval (-3271363276 / 1000000000000) (-3271360206 / 1000000000000)
      | 4 => orderedInterval (-2263653266 / 1000000000000) (-2263650933 / 1000000000000)
      | 5 => orderedInterval (-62016310 / 1000000000000) (-62014071 / 1000000000000)
      | 6 => orderedInterval (-3745014523 / 1000000000000) (-3745014279 / 1000000000000)
      | 7 => orderedInterval (-4246544673 / 1000000000000) (-4246544536 / 1000000000000)
      | _ => orderedInterval (-5943764225 / 1000000000000) (-5943764093 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10213441548 / 1000000000000) (-10213441507 / 1000000000000)
      | 1 => orderedInterval (2800995344 / 1000000000000) (2800995515 / 1000000000000)
      | 2 => orderedInterval (1718003577 / 1000000000000) (1718003622 / 1000000000000)
      | 3 => orderedInterval (9219437080 / 1000000000000) (9219443916 / 1000000000000)
      | 4 => orderedInterval (718816552 / 1000000000000) (718820587 / 1000000000000)
      | 5 => orderedInterval (3360236971 / 1000000000000) (3360241094 / 1000000000000)
      | 6 => orderedInterval (2340103 / 1000000000000) (2340278 / 1000000000000)
      | 7 => orderedInterval (294784080 / 1000000000000) (294784202 / 1000000000000)
      | _ => orderedInterval (2678427737 / 1000000000000) (2678427920 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14868438895 / 1000000000000) (14868438942 / 1000000000000)
      | 1 => orderedInterval (-557068805 / 1000000000000) (-557068699 / 1000000000000)
      | 2 => orderedInterval (-2900325349 / 1000000000000) (-2900325269 / 1000000000000)
      | 3 => orderedInterval (11882729548 / 1000000000000) (11882744815 / 1000000000000)
      | 4 => orderedInterval (4138745161 / 1000000000000) (4138752326 / 1000000000000)
      | 5 => orderedInterval (1247087303 / 1000000000000) (1247094913 / 1000000000000)
      | 6 => orderedInterval (5276615197 / 1000000000000) (5276615334 / 1000000000000)
      | 7 => orderedInterval (3721152933 / 1000000000000) (3721153046 / 1000000000000)
      | _ => orderedInterval (8569188996 / 1000000000000) (8569189263 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10204863773 / 1000000000000) (10204863828 / 1000000000000)
      | 1 => orderedInterval (-8086378386 / 1000000000000) (-8086378258 / 1000000000000)
      | 2 => orderedInterval (-4721955052 / 1000000000000) (-4721954906 / 1000000000000)
      | 3 => orderedInterval (-57354336834 / 1000000000000) (-57354302729 / 1000000000000)
      | 4 => orderedInterval (-1200776140 / 1000000000000) (-1200763106 / 1000000000000)
      | 5 => orderedInterval (-6517987836 / 1000000000000) (-6517973792 / 1000000000000)
      | 6 => orderedInterval (353261922 / 1000000000000) (353262038 / 1000000000000)
      | 7 => orderedInterval (-304739366 / 1000000000000) (-304739258 / 1000000000000)
      | _ => orderedInterval (-12427434194 / 1000000000000) (-12427433789 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16049918228 / 1000000000000) (-16049918164 / 1000000000000)
      | 1 => orderedInterval (2503291160 / 1000000000000) (2503291349 / 1000000000000)
      | 2 => orderedInterval (11684909903 / 1000000000000) (11684910173 / 1000000000000)
      | 3 => orderedInterval (-50143344412 / 1000000000000) (-50143268104 / 1000000000000)
      | 4 => orderedInterval (-4574588473 / 1000000000000) (-4574564121 / 1000000000000)
      | 5 => orderedInterval (-6043487165 / 1000000000000) (-6043461204 / 1000000000000)
      | 6 => orderedInterval (-5987470205 / 1000000000000) (-5987470101 / 1000000000000)
      | 7 => orderedInterval (-4092484221 / 1000000000000) (-4092484114 / 1000000000000)
      | _ => orderedInterval (-10805097335 / 1000000000000) (-10805096693 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-33448526847 / 1000000000000) (-33448518055 / 1000000000000)
    | 1 => orderedInterval (10579599896 / 1000000000000) (10579615627 / 1000000000000)
    | 2 => orderedInterval (46246563879 / 1000000000000) (46246594671 / 1000000000000)
    | 3 => orderedInterval (-80055482113 / 1000000000000) (-80055419972 / 1000000000000)
    | _ => orderedInterval (-83508188976 / 1000000000000) (-83508060979 / 1000000000000)

theorem compactCertificate559_stateChecks0 :
    compactCertificate559.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (861 / 2)) (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1268417406142761 / 4000000000000)) (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (410180127866313 / 800000000000)) (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks1 :
    compactCertificate559.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (370121035634427 / 4000000000000)) (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (994197163544319 / 4000000000000)) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2699438697913923 / 4000000000000)) (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks2 :
    compactCertificate559.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1988394327089499 / 4000000000000)) (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (3407147570563527 / 4000000000000)) (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2509689479556693 / 4000000000000)) (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks3 :
    compactCertificate559.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 307 12 (3850509057254139 / 4000000000000)) (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2223092440722531 / 4000000000000)) (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 314 12 (3944916547607679 / 4000000000000)) (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks4 :
    compactCertificate559.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3685852759890651 / 4000000000000)) (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2630398448903883 / 4000000000000)) (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2982591490632957 / 4000000000000)) (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks5 :
    compactCertificate559.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2486573834095533 / 4000000000000)) (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2196963392642193 / 4000000000000)) (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (636765621949107 / 800000000000)) (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks6 :
    compactCertificate559.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1761327221449929 / 4000000000000)) (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1493096591787969 / 4000000000000)) (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (934310520443307 / 4000000000000)) (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks7 :
    compactCertificate559.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (502475305270869 / 4000000000000)) (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1364318199179607 / 4000000000000)) (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1862859861829239 / 4000000000000)) (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_stateChecks8 :
    compactCertificate559.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (787689479556693 / 4000000000000)) (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3201914003185653 / 4000000000000)) (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2138730164421627 / 4000000000000)) (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_states : ∀ j,
    BesselStateValid (compactCertificate559.point j) (compactCertificate559.state j) :=
  compactCertificate559.statesValid_of_checks3 compactCertificate559_stateChecks0
    compactCertificate559_stateChecks1 compactCertificate559_stateChecks2
    compactCertificate559_stateChecks3 compactCertificate559_stateChecks4
    compactCertificate559_stateChecks5 compactCertificate559_stateChecks6
    compactCertificate559_stateChecks7 compactCertificate559_stateChecks8

theorem compactCertificate559_chunkChecks0_0 :
    compactCertificate559.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (861 / 2) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1268417406142761 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (410180127866313 / 800000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000)))) (orderedInterval (-14093899032 / 1000000000000) (-14093898996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (370121035634427 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2699438697913923 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000)))) (orderedInterval (-523108891 / 1000000000000) (-523108316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1988394327089499 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3407147570563527 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2509689479556693 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000)))) (orderedInterval (700837349 / 1000000000000) (700837375 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks0_1 :
    compactCertificate559.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3850509057254139 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2223092440722531 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3944916547607679 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000)))) (orderedInterval (-3271363276 / 1000000000000) (-3271360206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3685852759890651 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2630398448903883 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2982591490632957 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000)))) (orderedInterval (-2263653266 / 1000000000000) (-2263650933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2486573834095533 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2196963392642193 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (636765621949107 / 800000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000)))) (orderedInterval (-62016310 / 1000000000000) (-62014071 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks0_2 :
    compactCertificate559.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1761327221449929 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1493096591787969 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (934310520443307 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000)))) (orderedInterval (-3745014523 / 1000000000000) (-3745014279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (502475305270869 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1364318199179607 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1862859861829239 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000)))) (orderedInterval (-4246544673 / 1000000000000) (-4246544536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (787689479556693 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3201914003185653 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2138730164421627 / 4000000000000) 0 (IntervalRat.scale (861 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000)))) (orderedInterval (-5943764225 / 1000000000000) (-5943764093 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks0 :
    compactCertificate559.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate559.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate559_chunkChecks0_0
    compactCertificate559_chunkChecks0_1 compactCertificate559_chunkChecks0_2

theorem compactCertificate559_chunkChecks1_0 :
    compactCertificate559.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (861 / 2) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1268417406142761 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (410180127866313 / 800000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000)))) (orderedInterval (-10213441548 / 1000000000000) (-10213441507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (370121035634427 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2699438697913923 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000)))) (orderedInterval (2800995344 / 1000000000000) (2800995515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1988394327089499 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3407147570563527 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2509689479556693 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000)))) (orderedInterval (1718003577 / 1000000000000) (1718003622 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks1_1 :
    compactCertificate559.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3850509057254139 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2223092440722531 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3944916547607679 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000)))) (orderedInterval (9219437080 / 1000000000000) (9219443916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3685852759890651 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2630398448903883 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2982591490632957 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000)))) (orderedInterval (718816552 / 1000000000000) (718820587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2486573834095533 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2196963392642193 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (636765621949107 / 800000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000)))) (orderedInterval (3360236971 / 1000000000000) (3360241094 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks1_2 :
    compactCertificate559.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1761327221449929 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1493096591787969 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (934310520443307 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000)))) (orderedInterval (2340103 / 1000000000000) (2340278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (502475305270869 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1364318199179607 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1862859861829239 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000)))) (orderedInterval (294784080 / 1000000000000) (294784202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (787689479556693 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3201914003185653 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2138730164421627 / 4000000000000) 1 (IntervalRat.scale (861 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000)))) (orderedInterval (2678427737 / 1000000000000) (2678427920 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks1 :
    compactCertificate559.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate559.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate559_chunkChecks1_0
    compactCertificate559_chunkChecks1_1 compactCertificate559_chunkChecks1_2

theorem compactCertificate559_chunkChecks2_0 :
    compactCertificate559.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (861 / 2) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1268417406142761 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (410180127866313 / 800000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000)))) (orderedInterval (14868438895 / 1000000000000) (14868438942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (370121035634427 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2699438697913923 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000)))) (orderedInterval (-557068805 / 1000000000000) (-557068699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1988394327089499 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3407147570563527 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2509689479556693 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000)))) (orderedInterval (-2900325349 / 1000000000000) (-2900325269 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks2_1 :
    compactCertificate559.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3850509057254139 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2223092440722531 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3944916547607679 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000)))) (orderedInterval (11882729548 / 1000000000000) (11882744815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3685852759890651 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2630398448903883 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2982591490632957 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000)))) (orderedInterval (4138745161 / 1000000000000) (4138752326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2486573834095533 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2196963392642193 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (636765621949107 / 800000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000)))) (orderedInterval (1247087303 / 1000000000000) (1247094913 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks2_2 :
    compactCertificate559.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1761327221449929 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1493096591787969 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (934310520443307 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000)))) (orderedInterval (5276615197 / 1000000000000) (5276615334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (502475305270869 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1364318199179607 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1862859861829239 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000)))) (orderedInterval (3721152933 / 1000000000000) (3721153046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (787689479556693 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3201914003185653 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2138730164421627 / 4000000000000) 2 (IntervalRat.scale (861 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000)))) (orderedInterval (8569188996 / 1000000000000) (8569189263 / 1000000000000))) = true
  rfl'

theorem compactCertificate559_chunkChecks2 :
    compactCertificate559.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate559.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate559_chunkChecks2_0
    compactCertificate559_chunkChecks2_1 compactCertificate559_chunkChecks2_2

theorem compactCertificate559_chunkChecks3_0 :
    compactCertificate559.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (861 / 2) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1268417406142761 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (410180127866313 / 800000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000)))) (orderedInterval (10204863773 / 1000000000000) (10204863828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (370121035634427 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2699438697913923 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000)))) (orderedInterval (-8086378386 / 1000000000000) (-8086378258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1988394327089499 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3407147570563527 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2509689479556693 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000)))) (orderedInterval (-4721955052 / 1000000000000) (-4721954906 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate559_chunkChecks3_1 :
    compactCertificate559.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3850509057254139 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2223092440722531 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3944916547607679 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000)))) (orderedInterval (-57354336834 / 1000000000000) (-57354302729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3685852759890651 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2630398448903883 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2982591490632957 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000)))) (orderedInterval (-1200776140 / 1000000000000) (-1200763106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2486573834095533 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2196963392642193 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (636765621949107 / 800000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000)))) (orderedInterval (-6517987836 / 1000000000000) (-6517973792 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate559_chunkChecks3_2 :
    compactCertificate559.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1761327221449929 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1493096591787969 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (934310520443307 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000)))) (orderedInterval (353261922 / 1000000000000) (353262038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (502475305270869 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1364318199179607 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1862859861829239 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000)))) (orderedInterval (-304739366 / 1000000000000) (-304739258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (787689479556693 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3201914003185653 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2138730164421627 / 4000000000000) 3 (IntervalRat.scale (861 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000)))) (orderedInterval (-12427434194 / 1000000000000) (-12427433789 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate559_chunkChecks3 :
    compactCertificate559.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate559.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate559_chunkChecks3_0
    compactCertificate559_chunkChecks3_1 compactCertificate559_chunkChecks3_2

theorem compactCertificate559_chunkChecks4_0 :
    compactCertificate559.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (861 / 2) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29807500377 / 1000000000000) (-29807500376 / 1000000000000), orderedInterval (-24261558999 / 1000000000000) (-24261558998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1268417406142761 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24872488079 / 1000000000000) (-24872488078 / 1000000000000), orderedInterval (-37229585105 / 1000000000000) (-37229585104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (410180127866313 / 800000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34891721634 / 1000000000000) (-34891721545 / 1000000000000), orderedInterval (-4885996837 / 1000000000000) (-4885996748 / 1000000000000)))) (orderedInterval (-16049918228 / 1000000000000) (-16049918164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (370121035634427 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66662957774 / 1000000000000) (-66662909592 / 1000000000000), orderedInterval (49717547010 / 1000000000000) (49717595191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2699438697913923 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6176124797 / 1000000000000) (-6176124796 / 1000000000000), orderedInterval (-30081836923 / 1000000000000) (-30081836922 / 1000000000000)))) (orderedInterval (2503291160 / 1000000000000) (2503291349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1988394327089499 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35724803959 / 1000000000000) (35724804202 / 1000000000000), orderedInterval (2063780701 / 1000000000000) (2063780944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3407147570563527 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25485838230 / 1000000000000) (-25485838192 / 1000000000000), orderedInterval (-9877724157 / 1000000000000) (-9877724119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2509689479556693 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3527298979 / 1000000000000) (-3527298978 / 1000000000000), orderedInterval (31660629958 / 1000000000000) (31660629959 / 1000000000000)))) (orderedInterval (11684909903 / 1000000000000) (11684910173 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate559_chunkChecks4_1 :
    compactCertificate559.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3850509057254139 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22388622028 / 1000000000000) (22388638341 / 1000000000000), orderedInterval (-12664102397 / 1000000000000) (-12664086083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2223092440722531 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16118519484 / 1000000000000) (-16118519483 / 1000000000000), orderedInterval (-29745549598 / 1000000000000) (-29745549597 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3944916547607679 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13373185944 / 1000000000000) (13373185945 / 1000000000000), orderedInterval (21595694969 / 1000000000000) (21595694970 / 1000000000000)))) (orderedInterval (-50143344412 / 1000000000000) (-50143268104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3685852759890651 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25806566720 / 1000000000000) (-25806528879 / 1000000000000), orderedInterval (5004093680 / 1000000000000) (5004131522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2630398448903883 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30356423716 / 1000000000000) (-30356409345 / 1000000000000), orderedInterval (6848324297 / 1000000000000) (6848338669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2982591490632957 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27872309694 / 1000000000000) (-27872262520 / 1000000000000), orderedInterval (8788853589 / 1000000000000) (8788900764 / 1000000000000)))) (orderedInterval (-4574588473 / 1000000000000) (-4574564121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2486573834095533 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12264480482 / 1000000000000) (12264480483 / 1000000000000), orderedInterval (29548116382 / 1000000000000) (29548116383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2196963392642193 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8334017353 / 1000000000000) (-8334017352 / 1000000000000), orderedInterval (-33002032017 / 1000000000000) (-33002032016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (636765621949107 / 800000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26580687040 / 1000000000000) (-26580601214 / 1000000000000), orderedInterval (9675118594 / 1000000000000) (9675204420 / 1000000000000)))) (orderedInterval (-6043487165 / 1000000000000) (-6043461204 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate559_chunkChecks4_2 :
    compactCertificate559.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1761327221449929 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36575444232 / 1000000000000) (36575444239 / 1000000000000), orderedInterval (10351203491 / 1000000000000) (10351203498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1493096591787969 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8596210468 / 1000000000000) (-8596210467 / 1000000000000), orderedInterval (-40381659012 / 1000000000000) (-40381659011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (934310520443307 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49656397981 / 1000000000000) (49656402135 / 1000000000000), orderedInterval (-16223174473 / 1000000000000) (-16223170318 / 1000000000000)))) (orderedInterval (-5987470205 / 1000000000000) (-5987470101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (502475305270869 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47976604269 / 1000000000000) (47976604270 / 1000000000000), orderedInterval (52402941373 / 1000000000000) (52402941374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1364318199179607 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23277881450 / 1000000000000) (23277884227 / 1000000000000), orderedInterval (-36429533372 / 1000000000000) (-36429530595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1862859861829239 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36959689858 / 1000000000000) (36959690160 / 1000000000000), orderedInterval (936794358 / 1000000000000) (936794659 / 1000000000000)))) (orderedInterval (-4092484221 / 1000000000000) (-4092484114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (787689479556693 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (12030723234 / 1000000000000) (12030723314 / 1000000000000), orderedInterval (-55601380549 / 1000000000000) (-55601380470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3201914003185653 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4426558298 / 1000000000000) (-4426558297 / 1000000000000), orderedInterval (-27848711778 / 1000000000000) (-27848711777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2138730164421627 / 4000000000000) 4 (IntervalRat.scale (861 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33985700807 / 1000000000000) (33985700871 / 1000000000000), orderedInterval (5936607022 / 1000000000000) (5936607086 / 1000000000000)))) (orderedInterval (-10805097335 / 1000000000000) (-10805096693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate559_chunkChecks4 :
    compactCertificate559.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate559.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate559_chunkChecks4_0
    compactCertificate559_chunkChecks4_1 compactCertificate559_chunkChecks4_2

theorem compactCertificate559_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate559.chunkCheck r b = true :=
  compactCertificate559.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate559_chunkChecks0
    · exact compactCertificate559_chunkChecks1
    · exact compactCertificate559_chunkChecks2
    · exact compactCertificate559_chunkChecks3
    · exact compactCertificate559_chunkChecks4)

theorem compactCertificate559_coefficient0 :
    compactCertificate559.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate559_coefficient1 :
    compactCertificate559.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate559_coefficient2 :
    compactCertificate559.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate559_coefficient3 :
    compactCertificate559.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate559_coefficient4 :
    compactCertificate559.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate559_coefficients : ∀ r : Fin 5,
    compactCertificate559.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate559_coefficient0
  · exact compactCertificate559_coefficient1
  · exact compactCertificate559_coefficient2
  · exact compactCertificate559_coefficient3
  · exact compactCertificate559_coefficient4

theorem compactCertificate559_lower : (1 : ℚ) ≤ compactCertificate559.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate559, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate559_proves {t : ℝ} (ht : t ∈ compactCertificate559.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate559.proves compactCertificate559_states compactCertificate559_chunks
    compactCertificate559_coefficients compactCertificate559_lower ht

end Erdos232
