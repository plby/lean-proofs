/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate378 : CompactCertificate where
  left := 249
  right := 250
  center := 499 / 2
  grid := fun i =>
    match i.val with
    | 0 => 79
    | 1 => 59
    | 2 => 95
    | 3 => 17
    | 4 => 46
    | 5 => 125
    | 6 => 92
    | 7 => 157
    | 8 => 116
    | 9 => 178
    | 10 => 103
    | 11 => 182
    | 12 => 170
    | 13 => 121
    | 14 => 138
    | 15 => 115
    | 16 => 101
    | 17 => 147
    | 18 => 81
    | 19 => 69
    | 20 => 43
    | 21 => 23
    | 22 => 63
    | 23 => 86
    | 24 => 36
    | 25 => 148
    | _ => 99
  point := fun i =>
    match i.val with
    | 0 => 499 / 2
    | 1 => 735122283002599 / 4000000000000
    | 2 => 237723442282567 / 800000000000
    | 3 => 214506848759093 / 4000000000000
    | 4 => 576195568651121 / 4000000000000
    | 5 => 1564483054888557 / 4000000000000
    | 6 => 1152391137302741 / 4000000000000
    | 7 => 1974641855645993 / 4000000000000
    | 8 => 1454512253540987 / 4000000000000
    | 9 => 2231595841544501 / 4000000000000
    | 10 => 1288412459838029 / 4000000000000
    | 11 => 2286310519461361 / 4000000000000
    | 12 => 2136167859681109 / 4000000000000
    | 13 => 1524470181188197 / 4000000000000
    | 14 => 1728586705953363 / 4000000000000
    | 15 => 1441115381200547 / 4000000000000
    | 16 => 1273269143935487 / 4000000000000
    | 17 => 369043025961213 / 800000000000
    | 18 => 1020792431479111 / 4000000000000
    | 19 => 865337049131471 / 4000000000000
    | 20 => 541487746459013 / 4000000000000
    | 21 => 291213910952571 / 4000000000000
    | 22 => 790702417410713 / 4000000000000
    | 23 => 1079636551745401 / 4000000000000
    | 24 => 456512253540987 / 4000000000000
    | 25 => 1855696965841627 / 4000000000000
    | _ => 1239519572643893 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))
    | 1 => (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))
    | 2 => (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000))
    | 3 => (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))
    | 4 => (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))
    | 5 => (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000))
    | 6 => (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))
    | 7 => (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))
    | 8 => (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000))
    | 9 => (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))
    | 10 => (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))
    | 11 => (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000))
    | 12 => (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))
    | 13 => (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))
    | 14 => (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000))
    | 15 => (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))
    | 16 => (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))
    | 17 => (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000))
    | 18 => (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))
    | 19 => (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))
    | 20 => (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000))
    | 21 => (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))
    | 22 => (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))
    | 23 => (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000))
    | 24 => (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))
    | 25 => (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))
    | _ => (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15572395703 / 1000000000000) (-15572380515 / 1000000000000)
      | 1 => orderedInterval (-283574940 / 1000000000000) (-283573417 / 1000000000000)
      | 2 => orderedInterval (1026719040 / 1000000000000) (1026719055 / 1000000000000)
      | 3 => orderedInterval (7741908715 / 1000000000000) (7741909742 / 1000000000000)
      | 4 => orderedInterval (-4105300137 / 1000000000000) (-4105299840 / 1000000000000)
      | 5 => orderedInterval (2338946849 / 1000000000000) (2338947027 / 1000000000000)
      | 6 => orderedInterval (7067467402 / 1000000000000) (7067467473 / 1000000000000)
      | 7 => orderedInterval (499003641 / 1000000000000) (499003672 / 1000000000000)
      | _ => orderedInterval (-1766119918 / 1000000000000) (-1766119794 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7018376806 / 1000000000000) (7018391890 / 1000000000000)
      | 1 => orderedInterval (4621608390 / 1000000000000) (4621610765 / 1000000000000)
      | 2 => orderedInterval (2233894482 / 1000000000000) (2233894507 / 1000000000000)
      | 3 => orderedInterval (-5917662837 / 1000000000000) (-5917661363 / 1000000000000)
      | 4 => orderedInterval (-70567115 / 1000000000000) (-70566655 / 1000000000000)
      | 5 => orderedInterval (-3127881620 / 1000000000000) (-3127881388 / 1000000000000)
      | 6 => orderedInterval (2367231903 / 1000000000000) (2367231969 / 1000000000000)
      | 7 => orderedInterval (-2506266113 / 1000000000000) (-2506266086 / 1000000000000)
      | _ => orderedInterval (4427915140 / 1000000000000) (4427915300 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15165334794 / 1000000000000) (15165349872 / 1000000000000)
      | 1 => orderedInterval (4703485400 / 1000000000000) (4703489125 / 1000000000000)
      | 2 => orderedInterval (-4049469011 / 1000000000000) (-4049468966 / 1000000000000)
      | 3 => orderedInterval (-32304813293 / 1000000000000) (-32304811052 / 1000000000000)
      | 4 => orderedInterval (10467059736 / 1000000000000) (10467060450 / 1000000000000)
      | 5 => orderedInterval (-3380726181 / 1000000000000) (-3380725878 / 1000000000000)
      | 6 => orderedInterval (-8564860226 / 1000000000000) (-8564860162 / 1000000000000)
      | 7 => orderedInterval (1605105190 / 1000000000000) (1605105218 / 1000000000000)
      | _ => orderedInterval (1881048942 / 1000000000000) (1881049164 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6028411498 / 1000000000000) (-6028396457 / 1000000000000)
      | 1 => orderedInterval (-8229077412 / 1000000000000) (-8229071577 / 1000000000000)
      | 2 => orderedInterval (-6090012208 / 1000000000000) (-6090012128 / 1000000000000)
      | 3 => orderedInterval (16589278842 / 1000000000000) (16589282486 / 1000000000000)
      | 4 => orderedInterval (2486589806 / 1000000000000) (2486590919 / 1000000000000)
      | 5 => orderedInterval (8448036661 / 1000000000000) (8448037061 / 1000000000000)
      | 6 => orderedInterval (-2142364333 / 1000000000000) (-2142364271 / 1000000000000)
      | 7 => orderedInterval (3527019299 / 1000000000000) (3527019327 / 1000000000000)
      | _ => orderedInterval (3509776496 / 1000000000000) (3509776817 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14451545090 / 1000000000000) (-14451530001 / 1000000000000)
      | 1 => orderedInterval (-12189822674 / 1000000000000) (-12189813507 / 1000000000000)
      | 2 => orderedInterval (15911515268 / 1000000000000) (15911515416 / 1000000000000)
      | 3 => orderedInterval (153230671692 / 1000000000000) (153230678097 / 1000000000000)
      | 4 => orderedInterval (-28626444544 / 1000000000000) (-28626442799 / 1000000000000)
      | 5 => orderedInterval (3976251445 / 1000000000000) (3976251981 / 1000000000000)
      | 6 => orderedInterval (9168088371 / 1000000000000) (9168088432 / 1000000000000)
      | 7 => orderedInterval (-2275342806 / 1000000000000) (-2275342776 / 1000000000000)
      | _ => orderedInterval (1789279016 / 1000000000000) (1789279500 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3053345051 / 1000000000000) (-3053326597 / 1000000000000)
    | 1 => orderedInterval (9046649036 / 1000000000000) (9046668939 / 1000000000000)
    | 2 => orderedInterval (-14477834649 / 1000000000000) (-14477812229 / 1000000000000)
    | 3 => orderedInterval (12070835653 / 1000000000000) (12070862177 / 1000000000000)
    | _ => orderedInterval (126532650678 / 1000000000000) (126532684343 / 1000000000000)

theorem compactCertificate378_stateChecks0 :
    compactCertificate378.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (499 / 2)) (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (735122283002599 / 4000000000000)) (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (237723442282567 / 800000000000)) (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks1 :
    compactCertificate378.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (214506848759093 / 4000000000000)) (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (576195568651121 / 4000000000000)) (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1564483054888557 / 4000000000000)) (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks2 :
    compactCertificate378.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1152391137302741 / 4000000000000)) (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1974641855645993 / 4000000000000)) (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1454512253540987 / 4000000000000)) (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks3 :
    compactCertificate378.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2231595841544501 / 4000000000000)) (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1288412459838029 / 4000000000000)) (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2286310519461361 / 4000000000000)) (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks4 :
    compactCertificate378.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2136167859681109 / 4000000000000)) (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1524470181188197 / 4000000000000)) (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1728586705953363 / 4000000000000)) (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks5 :
    compactCertificate378.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1441115381200547 / 4000000000000)) (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1273269143935487 / 4000000000000)) (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (369043025961213 / 800000000000)) (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks6 :
    compactCertificate378.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1020792431479111 / 4000000000000)) (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (865337049131471 / 4000000000000)) (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (541487746459013 / 4000000000000)) (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks7 :
    compactCertificate378.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (291213910952571 / 4000000000000)) (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (790702417410713 / 4000000000000)) (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1079636551745401 / 4000000000000)) (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_stateChecks8 :
    compactCertificate378.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (456512253540987 / 4000000000000)) (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1855696965841627 / 4000000000000)) (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1239519572643893 / 4000000000000)) (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_states : ∀ j,
    BesselStateValid (compactCertificate378.point j) (compactCertificate378.state j) :=
  compactCertificate378.statesValid_of_checks3 compactCertificate378_stateChecks0
    compactCertificate378_stateChecks1 compactCertificate378_stateChecks2
    compactCertificate378_stateChecks3 compactCertificate378_stateChecks4
    compactCertificate378_stateChecks5 compactCertificate378_stateChecks6
    compactCertificate378_stateChecks7 compactCertificate378_stateChecks8

theorem compactCertificate378_chunkChecks0_0 :
    compactCertificate378.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (499 / 2) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (735122283002599 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (237723442282567 / 800000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000)))) (orderedInterval (-15572395703 / 1000000000000) (-15572380515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (214506848759093 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (576195568651121 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1564483054888557 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000)))) (orderedInterval (-283574940 / 1000000000000) (-283573417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1152391137302741 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1974641855645993 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1454512253540987 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000)))) (orderedInterval (1026719040 / 1000000000000) (1026719055 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks0_1 :
    compactCertificate378.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2231595841544501 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1288412459838029 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2286310519461361 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000)))) (orderedInterval (7741908715 / 1000000000000) (7741909742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2136167859681109 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1524470181188197 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1728586705953363 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000)))) (orderedInterval (-4105300137 / 1000000000000) (-4105299840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1441115381200547 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1273269143935487 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (369043025961213 / 800000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000)))) (orderedInterval (2338946849 / 1000000000000) (2338947027 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks0_2 :
    compactCertificate378.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1020792431479111 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (865337049131471 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (541487746459013 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000)))) (orderedInterval (7067467402 / 1000000000000) (7067467473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (291213910952571 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (790702417410713 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1079636551745401 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000)))) (orderedInterval (499003641 / 1000000000000) (499003672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (456512253540987 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1855696965841627 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1239519572643893 / 4000000000000) 0 (IntervalRat.scale (499 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000)))) (orderedInterval (-1766119918 / 1000000000000) (-1766119794 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks0 :
    compactCertificate378.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate378.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate378_chunkChecks0_0
    compactCertificate378_chunkChecks0_1 compactCertificate378_chunkChecks0_2

theorem compactCertificate378_chunkChecks1_0 :
    compactCertificate378.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (499 / 2) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (735122283002599 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (237723442282567 / 800000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000)))) (orderedInterval (7018376806 / 1000000000000) (7018391890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (214506848759093 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (576195568651121 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1564483054888557 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000)))) (orderedInterval (4621608390 / 1000000000000) (4621610765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1152391137302741 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1974641855645993 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1454512253540987 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000)))) (orderedInterval (2233894482 / 1000000000000) (2233894507 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks1_1 :
    compactCertificate378.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2231595841544501 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1288412459838029 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2286310519461361 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000)))) (orderedInterval (-5917662837 / 1000000000000) (-5917661363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2136167859681109 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1524470181188197 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1728586705953363 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000)))) (orderedInterval (-70567115 / 1000000000000) (-70566655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1441115381200547 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1273269143935487 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (369043025961213 / 800000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000)))) (orderedInterval (-3127881620 / 1000000000000) (-3127881388 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks1_2 :
    compactCertificate378.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1020792431479111 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (865337049131471 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (541487746459013 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000)))) (orderedInterval (2367231903 / 1000000000000) (2367231969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (291213910952571 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (790702417410713 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1079636551745401 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000)))) (orderedInterval (-2506266113 / 1000000000000) (-2506266086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (456512253540987 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1855696965841627 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1239519572643893 / 4000000000000) 1 (IntervalRat.scale (499 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000)))) (orderedInterval (4427915140 / 1000000000000) (4427915300 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks1 :
    compactCertificate378.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate378.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate378_chunkChecks1_0
    compactCertificate378_chunkChecks1_1 compactCertificate378_chunkChecks1_2

theorem compactCertificate378_chunkChecks2_0 :
    compactCertificate378.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (499 / 2) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (735122283002599 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (237723442282567 / 800000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000)))) (orderedInterval (15165334794 / 1000000000000) (15165349872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (214506848759093 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (576195568651121 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1564483054888557 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000)))) (orderedInterval (4703485400 / 1000000000000) (4703489125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1152391137302741 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1974641855645993 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1454512253540987 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000)))) (orderedInterval (-4049469011 / 1000000000000) (-4049468966 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks2_1 :
    compactCertificate378.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2231595841544501 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1288412459838029 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2286310519461361 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000)))) (orderedInterval (-32304813293 / 1000000000000) (-32304811052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2136167859681109 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1524470181188197 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1728586705953363 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000)))) (orderedInterval (10467059736 / 1000000000000) (10467060450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1441115381200547 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1273269143935487 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (369043025961213 / 800000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000)))) (orderedInterval (-3380726181 / 1000000000000) (-3380725878 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks2_2 :
    compactCertificate378.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1020792431479111 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (865337049131471 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (541487746459013 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000)))) (orderedInterval (-8564860226 / 1000000000000) (-8564860162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (291213910952571 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (790702417410713 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1079636551745401 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000)))) (orderedInterval (1605105190 / 1000000000000) (1605105218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (456512253540987 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1855696965841627 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1239519572643893 / 4000000000000) 2 (IntervalRat.scale (499 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000)))) (orderedInterval (1881048942 / 1000000000000) (1881049164 / 1000000000000))) = true
  rfl'

theorem compactCertificate378_chunkChecks2 :
    compactCertificate378.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate378.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate378_chunkChecks2_0
    compactCertificate378_chunkChecks2_1 compactCertificate378_chunkChecks2_2

theorem compactCertificate378_chunkChecks3_0 :
    compactCertificate378.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (499 / 2) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (735122283002599 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (237723442282567 / 800000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000)))) (orderedInterval (-6028411498 / 1000000000000) (-6028396457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (214506848759093 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (576195568651121 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1564483054888557 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000)))) (orderedInterval (-8229077412 / 1000000000000) (-8229071577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1152391137302741 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1974641855645993 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1454512253540987 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000)))) (orderedInterval (-6090012208 / 1000000000000) (-6090012128 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate378_chunkChecks3_1 :
    compactCertificate378.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2231595841544501 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1288412459838029 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2286310519461361 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000)))) (orderedInterval (16589278842 / 1000000000000) (16589282486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2136167859681109 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1524470181188197 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1728586705953363 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000)))) (orderedInterval (2486589806 / 1000000000000) (2486590919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1441115381200547 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1273269143935487 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (369043025961213 / 800000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000)))) (orderedInterval (8448036661 / 1000000000000) (8448037061 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate378_chunkChecks3_2 :
    compactCertificate378.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1020792431479111 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (865337049131471 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (541487746459013 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000)))) (orderedInterval (-2142364333 / 1000000000000) (-2142364271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (291213910952571 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (790702417410713 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1079636551745401 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000)))) (orderedInterval (3527019299 / 1000000000000) (3527019327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (456512253540987 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1855696965841627 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1239519572643893 / 4000000000000) 3 (IntervalRat.scale (499 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000)))) (orderedInterval (3509776496 / 1000000000000) (3509776817 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate378_chunkChecks3 :
    compactCertificate378.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate378.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate378_chunkChecks3_0
    compactCertificate378_chunkChecks3_1 compactCertificate378_chunkChecks3_2

theorem compactCertificate378_chunkChecks4_0 :
    compactCertificate378.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (499 / 2) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43626937395 / 1000000000000) (-43626900627 / 1000000000000), orderedInterval (25548587880 / 1000000000000) (25548624648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (735122283002599 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41753591973 / 1000000000000) (41753644211 / 1000000000000), orderedInterval (-41594414833 / 1000000000000) (-41594362596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (237723442282567 / 800000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22677346853 / 1000000000000) (22677348736 / 1000000000000), orderedInterval (-40388218275 / 1000000000000) (-40388216391 / 1000000000000)))) (orderedInterval (-14451545090 / 1000000000000) (-14451530001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (214506848759093 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91839853524 / 1000000000000) (-91839853523 / 1000000000000), orderedInterval (-57765817069 / 1000000000000) (-57765817068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (576195568651121 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20922166682 / 1000000000000) (20922166683 / 1000000000000), orderedInterval (63028523266 / 1000000000000) (63028523267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1564483054888557 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28750680630 / 1000000000000) (28750701623 / 1000000000000), orderedInterval (-28340095644 / 1000000000000) (-28340074651 / 1000000000000)))) (orderedInterval (-12189822674 / 1000000000000) (-12189813507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1152391137302741 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6735307704 / 1000000000000) (-6735307690 / 1000000000000), orderedInterval (46534520972 / 1000000000000) (46534520987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1974641855645993 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33668766811 / 1000000000000) (-33668766808 / 1000000000000), orderedInterval (-12456054782 / 1000000000000) (-12456054779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1454512253540987 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-486611077 / 1000000000000) (-486611076 / 1000000000000), orderedInterval (41839756094 / 1000000000000) (41839756096 / 1000000000000)))) (orderedInterval (15911515268 / 1000000000000) (15911515416 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate378_chunkChecks4_1 :
    compactCertificate378.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2231595841544501 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16765881599 / 1000000000000) (-16765881177 / 1000000000000), orderedInterval (29340914037 / 1000000000000) (29340914459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1288412459838029 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28501095525 / 1000000000000) (28501107030 / 1000000000000), orderedInterval (-34163666712 / 1000000000000) (-34163655206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2286310519461361 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18649367468 / 1000000000000) (18649367469 / 1000000000000), orderedInterval (27660306511 / 1000000000000) (27660306512 / 1000000000000)))) (orderedInterval (153230671692 / 1000000000000) (153230678097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2136167859681109 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23695228455 / 1000000000000) (23695228456 / 1000000000000), orderedInterval (25089851307 / 1000000000000) (25089851308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1524470181188197 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40063080418 / 1000000000000) (-40063077729 / 1000000000000), orderedInterval (8136558499 / 1000000000000) (8136561189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1728586705953363 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21924696528 / 1000000000000) (-21924693961 / 1000000000000), orderedInterval (31528774878 / 1000000000000) (31528777444 / 1000000000000)))) (orderedInterval (-28626444544 / 1000000000000) (-28626442799 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1441115381200547 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9143066488 / 1000000000000) (9143066514 / 1000000000000), orderedInterval (-41042256876 / 1000000000000) (-41042256850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1273269143935487 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-43536648754 / 1000000000000) (-43536646073 / 1000000000000), orderedInterval (10291476824 / 1000000000000) (10291479505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (369043025961213 / 800000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10080157008 / 1000000000000) (-10080157007 / 1000000000000), orderedInterval (-35744293197 / 1000000000000) (-35744293196 / 1000000000000)))) (orderedInterval (3976251445 / 1000000000000) (3976251981 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate378_chunkChecks4_2 :
    compactCertificate378.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1020792431479111 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-49865518935 / 1000000000000) (-49865518890 / 1000000000000), orderedInterval (-2736969485 / 1000000000000) (-2736969440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (865337049131471 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18559919107 / 1000000000000) (-18559919106 / 1000000000000), orderedInterval (-50930579600 / 1000000000000) (-50930579599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (541487746459013 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60086821512 / 1000000000000) (-60086821511 / 1000000000000), orderedInterval (-32828066976 / 1000000000000) (-32828066975 / 1000000000000)))) (orderedInterval (9168088371 / 1000000000000) (9168088432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (291213910952571 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-90824020384 / 1000000000000) (-90824020383 / 1000000000000), orderedInterval (-21628770603 / 1000000000000) (-21628770602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (790702417410713 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29178619727 / 1000000000000) (-29178619726 / 1000000000000), orderedInterval (-48600016355 / 1000000000000) (-48600016354 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1079636551745401 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24009276564 / 1000000000000) (24009276565 / 1000000000000), orderedInterval (42171651547 / 1000000000000) (42171651548 / 1000000000000)))) (orderedInterval (-2275342806 / 1000000000000) (-2275342776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (456512253540987 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72469948532 / 1000000000000) (72469949496 / 1000000000000), orderedInterval (-18377857623 / 1000000000000) (-18377856660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1855696965841627 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9033465901 / 1000000000000) (-9033465884 / 1000000000000), orderedInterval (35935306446 / 1000000000000) (35935306464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1239519572643893 / 4000000000000) 4 (IntervalRat.scale (499 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15660539469 / 1000000000000) (15660539718 / 1000000000000), orderedInterval (-42559462871 / 1000000000000) (-42559462623 / 1000000000000)))) (orderedInterval (1789279016 / 1000000000000) (1789279500 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate378_chunkChecks4 :
    compactCertificate378.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate378.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate378_chunkChecks4_0
    compactCertificate378_chunkChecks4_1 compactCertificate378_chunkChecks4_2

theorem compactCertificate378_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate378.chunkCheck r b = true :=
  compactCertificate378.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate378_chunkChecks0
    · exact compactCertificate378_chunkChecks1
    · exact compactCertificate378_chunkChecks2
    · exact compactCertificate378_chunkChecks3
    · exact compactCertificate378_chunkChecks4)

theorem compactCertificate378_coefficient0 :
    compactCertificate378.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate378_coefficient1 :
    compactCertificate378.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate378_coefficient2 :
    compactCertificate378.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate378_coefficient3 :
    compactCertificate378.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate378_coefficient4 :
    compactCertificate378.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate378_coefficients : ∀ r : Fin 5,
    compactCertificate378.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate378_coefficient0
  · exact compactCertificate378_coefficient1
  · exact compactCertificate378_coefficient2
  · exact compactCertificate378_coefficient3
  · exact compactCertificate378_coefficient4

theorem compactCertificate378_lower : (1 : ℚ) ≤ compactCertificate378.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate378, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate378_proves {t : ℝ} (ht : t ∈ compactCertificate378.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate378.proves compactCertificate378_states compactCertificate378_chunks
    compactCertificate378_coefficients compactCertificate378_lower ht

end Erdos232
