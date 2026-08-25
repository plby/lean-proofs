/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate451 : CompactCertificate where
  left := 322
  right := 323
  center := 645 / 2
  grid := fun i =>
    match i.val with
    | 0 => 103
    | 1 => 76
    | 2 => 122
    | 3 => 22
    | 4 => 59
    | 5 => 161
    | 6 => 119
    | 7 => 203
    | 8 => 150
    | 9 => 230
    | 10 => 133
    | 11 => 235
    | 12 => 220
    | 13 => 157
    | 14 => 178
    | 15 => 148
    | 16 => 131
    | 17 => 190
    | 18 => 105
    | 19 => 89
    | 20 => 56
    | 21 => 30
    | 22 => 81
    | 23 => 111
    | 24 => 47
    | 25 => 191
    | _ => 128
  point := fun i =>
    match i.val with
    | 0 => 645 / 2
    | 1 => 190041632279229 / 800000000000
    | 2 => 61455559227357 / 160000000000
    | 3 => 55453674328503 / 800000000000
    | 4 => 148956369450891 / 800000000000
    | 5 => 404445519199647 / 800000000000
    | 6 => 297912738901911 / 800000000000
    | 7 => 510478555868403 / 800000000000
    | 8 => 376016193801177 / 800000000000
    | 9 => 576905538194871 / 800000000000
    | 10 => 333076567773759 / 800000000000
    | 11 => 591050214449931 / 800000000000
    | 12 => 552235779356439 / 800000000000
    | 13 => 394101509766087 / 800000000000
    | 14 => 446869108352673 / 800000000000
    | 15 => 372552874097937 / 800000000000
    | 16 => 329161762660677 / 800000000000
    | 17 => 95403908515023 / 160000000000
    | 18 => 263892231785181 / 800000000000
    | 19 => 223704367410741 / 800000000000
    | 20 => 139983806198823 / 800000000000
    | 21 => 75283756538841 / 800000000000
    | 22 => 204410043779523 / 800000000000
    | 23 => 279104439228771 / 800000000000
    | 24 => 118016193801177 / 800000000000
    | 25 => 479729275738617 / 800000000000
    | _ => 320436923589303 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))
    | 1 => (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))
    | 2 => (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000))
    | 3 => (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))
    | 4 => (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
    | 5 => (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000))
    | 6 => (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))
    | 7 => (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))
    | 8 => (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000))
    | 9 => (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))
    | 10 => (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))
    | 11 => (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000))
    | 12 => (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))
    | 13 => (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))
    | 14 => (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000))
    | 15 => (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))
    | 16 => (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))
    | 17 => (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000))
    | 18 => (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))
    | 19 => (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))
    | 20 => (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000))
    | 21 => (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))
    | 22 => (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))
    | 23 => (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000))
    | 24 => (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))
    | 25 => (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))
    | _ => (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (7376809636 / 1000000000000) (7376809735 / 1000000000000)
      | 1 => orderedInterval (-1689246226 / 1000000000000) (-1689246182 / 1000000000000)
      | 2 => orderedInterval (511631779 / 1000000000000) (511631803 / 1000000000000)
      | 3 => orderedInterval (1014063385 / 1000000000000) (1014064218 / 1000000000000)
      | 4 => orderedInterval (-605219959 / 1000000000000) (-605219920 / 1000000000000)
      | 5 => orderedInterval (1987766258 / 1000000000000) (1987766292 / 1000000000000)
      | 6 => orderedInterval (6596151838 / 1000000000000) (6596151921 / 1000000000000)
      | 7 => orderedInterval (2847523801 / 1000000000000) (2847523898 / 1000000000000)
      | _ => orderedInterval (6126812767 / 1000000000000) (6126816601 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16622417035 / 1000000000000) (-16622416931 / 1000000000000)
      | 1 => orderedInterval (3327852733 / 1000000000000) (3327852781 / 1000000000000)
      | 2 => orderedInterval (1980414657 / 1000000000000) (1980414698 / 1000000000000)
      | 3 => orderedInterval (-14601803754 / 1000000000000) (-14601802438 / 1000000000000)
      | 4 => orderedInterval (-6568291832 / 1000000000000) (-6568291768 / 1000000000000)
      | 5 => orderedInterval (3773089046 / 1000000000000) (3773089095 / 1000000000000)
      | 6 => orderedInterval (7741199319 / 1000000000000) (7741199395 / 1000000000000)
      | 7 => orderedInterval (1475279311 / 1000000000000) (1475279392 / 1000000000000)
      | _ => orderedInterval (-2137944111 / 1000000000000) (-2137939335 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8415129793 / 1000000000000) (-8415129682 / 1000000000000)
      | 1 => orderedInterval (-2476897873 / 1000000000000) (-2476897809 / 1000000000000)
      | 2 => orderedInterval (-2678192450 / 1000000000000) (-2678192380 / 1000000000000)
      | 3 => orderedInterval (2208150780 / 1000000000000) (2208153025 / 1000000000000)
      | 4 => orderedInterval (1364846044 / 1000000000000) (1364846148 / 1000000000000)
      | 5 => orderedInterval (-3676545509 / 1000000000000) (-3676545436 / 1000000000000)
      | 6 => orderedInterval (-6589171682 / 1000000000000) (-6589171609 / 1000000000000)
      | 7 => orderedInterval (-3728383189 / 1000000000000) (-3728383117 / 1000000000000)
      | _ => orderedInterval (-11753809524 / 1000000000000) (-11753803550 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16842476192 / 1000000000000) (16842476313 / 1000000000000)
      | 1 => orderedInterval (-8312566407 / 1000000000000) (-8312566314 / 1000000000000)
      | 2 => orderedInterval (-5637036134 / 1000000000000) (-5637036013 / 1000000000000)
      | 3 => orderedInterval (64043406471 / 1000000000000) (64043410590 / 1000000000000)
      | 4 => orderedInterval (18147996808 / 1000000000000) (18147996984 / 1000000000000)
      | 5 => orderedInterval (-8879515757 / 1000000000000) (-8879515647 / 1000000000000)
      | 6 => orderedInterval (-6815211553 / 1000000000000) (-6815211482 / 1000000000000)
      | 7 => orderedInterval (-2223820081 / 1000000000000) (-2223820016 / 1000000000000)
      | _ => orderedInterval (-5542852776 / 1000000000000) (-5542845300 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9828553220 / 1000000000000) (9828553354 / 1000000000000)
      | 1 => orderedInterval (7718802817 / 1000000000000) (7718802958 / 1000000000000)
      | 2 => orderedInterval (11916829955 / 1000000000000) (11916830172 / 1000000000000)
      | 3 => orderedInterval (-26863450421 / 1000000000000) (-26863442341 / 1000000000000)
      | 4 => orderedInterval (-2909348246 / 1000000000000) (-2909347941 / 1000000000000)
      | 5 => orderedInterval (7227922839 / 1000000000000) (7227923013 / 1000000000000)
      | 6 => orderedInterval (6547521874 / 1000000000000) (6547521943 / 1000000000000)
      | 7 => orderedInterval (4082657924 / 1000000000000) (4082657985 / 1000000000000)
      | _ => orderedInterval (25122218992 / 1000000000000) (25122228403 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (24166293279 / 1000000000000) (24166298366 / 1000000000000)
    | 1 => orderedInterval (-21632621666 / 1000000000000) (-21632615111 / 1000000000000)
    | 2 => orderedInterval (-35745133196 / 1000000000000) (-35745124410 / 1000000000000)
    | 3 => orderedInterval (61622876763 / 1000000000000) (61622889115 / 1000000000000)
    | _ => orderedInterval (42671708954 / 1000000000000) (42671727546 / 1000000000000)

theorem compactCertificate451_stateChecks0 :
    compactCertificate451.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (645 / 2)) (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (190041632279229 / 800000000000)) (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (61455559227357 / 160000000000)) (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks1 :
    compactCertificate451.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (55453674328503 / 800000000000)) (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148956369450891 / 800000000000)) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (404445519199647 / 800000000000)) (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks2 :
    compactCertificate451.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (297912738901911 / 800000000000)) (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (510478555868403 / 800000000000)) (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (376016193801177 / 800000000000)) (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks3 :
    compactCertificate451.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (576905538194871 / 800000000000)) (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (333076567773759 / 800000000000)) (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (591050214449931 / 800000000000)) (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks4 :
    compactCertificate451.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (552235779356439 / 800000000000)) (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (394101509766087 / 800000000000)) (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (446869108352673 / 800000000000)) (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks5 :
    compactCertificate451.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (372552874097937 / 800000000000)) (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (329161762660677 / 800000000000)) (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (95403908515023 / 160000000000)) (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks6 :
    compactCertificate451.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (263892231785181 / 800000000000)) (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (223704367410741 / 800000000000)) (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (139983806198823 / 800000000000)) (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks7 :
    compactCertificate451.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (75283756538841 / 800000000000)) (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (204410043779523 / 800000000000)) (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (279104439228771 / 800000000000)) (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_stateChecks8 :
    compactCertificate451.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (118016193801177 / 800000000000)) (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (479729275738617 / 800000000000)) (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (320436923589303 / 800000000000)) (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_states : ∀ j,
    BesselStateValid (compactCertificate451.point j) (compactCertificate451.state j) :=
  compactCertificate451.statesValid_of_checks3 compactCertificate451_stateChecks0
    compactCertificate451_stateChecks1 compactCertificate451_stateChecks2
    compactCertificate451_stateChecks3 compactCertificate451_stateChecks4
    compactCertificate451_stateChecks5 compactCertificate451_stateChecks6
    compactCertificate451_stateChecks7 compactCertificate451_stateChecks8

theorem compactCertificate451_chunkChecks0_0 :
    compactCertificate451.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (645 / 2) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (190041632279229 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (61455559227357 / 160000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000)))) (orderedInterval (7376809636 / 1000000000000) (7376809735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (55453674328503 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (404445519199647 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000)))) (orderedInterval (-1689246226 / 1000000000000) (-1689246182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (297912738901911 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (510478555868403 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (376016193801177 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000)))) (orderedInterval (511631779 / 1000000000000) (511631803 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks0_1 :
    compactCertificate451.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (576905538194871 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (333076567773759 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (591050214449931 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000)))) (orderedInterval (1014063385 / 1000000000000) (1014064218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (552235779356439 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (394101509766087 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (446869108352673 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000)))) (orderedInterval (-605219959 / 1000000000000) (-605219920 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (372552874097937 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (329161762660677 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (95403908515023 / 160000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000)))) (orderedInterval (1987766258 / 1000000000000) (1987766292 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks0_2 :
    compactCertificate451.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (263892231785181 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (223704367410741 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (139983806198823 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000)))) (orderedInterval (6596151838 / 1000000000000) (6596151921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (75283756538841 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (204410043779523 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (279104439228771 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000)))) (orderedInterval (2847523801 / 1000000000000) (2847523898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (118016193801177 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (479729275738617 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (320436923589303 / 800000000000) 0 (IntervalRat.scale (645 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000)))) (orderedInterval (6126812767 / 1000000000000) (6126816601 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks0 :
    compactCertificate451.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate451.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate451_chunkChecks0_0
    compactCertificate451_chunkChecks0_1 compactCertificate451_chunkChecks0_2

theorem compactCertificate451_chunkChecks1_0 :
    compactCertificate451.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (645 / 2) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (190041632279229 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (61455559227357 / 160000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000)))) (orderedInterval (-16622417035 / 1000000000000) (-16622416931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (55453674328503 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (404445519199647 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000)))) (orderedInterval (3327852733 / 1000000000000) (3327852781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (297912738901911 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (510478555868403 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (376016193801177 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000)))) (orderedInterval (1980414657 / 1000000000000) (1980414698 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks1_1 :
    compactCertificate451.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (576905538194871 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (333076567773759 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (591050214449931 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000)))) (orderedInterval (-14601803754 / 1000000000000) (-14601802438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (552235779356439 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (394101509766087 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (446869108352673 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000)))) (orderedInterval (-6568291832 / 1000000000000) (-6568291768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (372552874097937 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (329161762660677 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (95403908515023 / 160000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000)))) (orderedInterval (3773089046 / 1000000000000) (3773089095 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks1_2 :
    compactCertificate451.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (263892231785181 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (223704367410741 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (139983806198823 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000)))) (orderedInterval (7741199319 / 1000000000000) (7741199395 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (75283756538841 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (204410043779523 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (279104439228771 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000)))) (orderedInterval (1475279311 / 1000000000000) (1475279392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (118016193801177 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (479729275738617 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (320436923589303 / 800000000000) 1 (IntervalRat.scale (645 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000)))) (orderedInterval (-2137944111 / 1000000000000) (-2137939335 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks1 :
    compactCertificate451.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate451.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate451_chunkChecks1_0
    compactCertificate451_chunkChecks1_1 compactCertificate451_chunkChecks1_2

theorem compactCertificate451_chunkChecks2_0 :
    compactCertificate451.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (645 / 2) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (190041632279229 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (61455559227357 / 160000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000)))) (orderedInterval (-8415129793 / 1000000000000) (-8415129682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (55453674328503 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (404445519199647 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000)))) (orderedInterval (-2476897873 / 1000000000000) (-2476897809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (297912738901911 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (510478555868403 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (376016193801177 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000)))) (orderedInterval (-2678192450 / 1000000000000) (-2678192380 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks2_1 :
    compactCertificate451.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (576905538194871 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (333076567773759 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (591050214449931 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000)))) (orderedInterval (2208150780 / 1000000000000) (2208153025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (552235779356439 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (394101509766087 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (446869108352673 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000)))) (orderedInterval (1364846044 / 1000000000000) (1364846148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (372552874097937 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (329161762660677 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (95403908515023 / 160000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000)))) (orderedInterval (-3676545509 / 1000000000000) (-3676545436 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks2_2 :
    compactCertificate451.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (263892231785181 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (223704367410741 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (139983806198823 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000)))) (orderedInterval (-6589171682 / 1000000000000) (-6589171609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (75283756538841 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (204410043779523 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (279104439228771 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000)))) (orderedInterval (-3728383189 / 1000000000000) (-3728383117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (118016193801177 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (479729275738617 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (320436923589303 / 800000000000) 2 (IntervalRat.scale (645 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000)))) (orderedInterval (-11753809524 / 1000000000000) (-11753803550 / 1000000000000))) = true
  rfl'

theorem compactCertificate451_chunkChecks2 :
    compactCertificate451.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate451.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate451_chunkChecks2_0
    compactCertificate451_chunkChecks2_1 compactCertificate451_chunkChecks2_2

theorem compactCertificate451_chunkChecks3_0 :
    compactCertificate451.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (645 / 2) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (190041632279229 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (61455559227357 / 160000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000)))) (orderedInterval (16842476192 / 1000000000000) (16842476313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (55453674328503 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (404445519199647 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000)))) (orderedInterval (-8312566407 / 1000000000000) (-8312566314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (297912738901911 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (510478555868403 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (376016193801177 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000)))) (orderedInterval (-5637036134 / 1000000000000) (-5637036013 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate451_chunkChecks3_1 :
    compactCertificate451.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (576905538194871 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (333076567773759 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (591050214449931 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000)))) (orderedInterval (64043406471 / 1000000000000) (64043410590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (552235779356439 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (394101509766087 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (446869108352673 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000)))) (orderedInterval (18147996808 / 1000000000000) (18147996984 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (372552874097937 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (329161762660677 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (95403908515023 / 160000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000)))) (orderedInterval (-8879515757 / 1000000000000) (-8879515647 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate451_chunkChecks3_2 :
    compactCertificate451.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (263892231785181 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (223704367410741 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (139983806198823 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000)))) (orderedInterval (-6815211553 / 1000000000000) (-6815211482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (75283756538841 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (204410043779523 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (279104439228771 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000)))) (orderedInterval (-2223820081 / 1000000000000) (-2223820016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (118016193801177 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (479729275738617 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (320436923589303 / 800000000000) 3 (IntervalRat.scale (645 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000)))) (orderedInterval (-5542852776 / 1000000000000) (-5542845300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate451_chunkChecks3 :
    compactCertificate451.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate451.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate451_chunkChecks3_0
    compactCertificate451_chunkChecks3_1 compactCertificate451_chunkChecks3_2

theorem compactCertificate451_chunkChecks4_0 :
    compactCertificate451.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (645 / 2) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13088859782 / 1000000000000) (13088859892 / 1000000000000), orderedInterval (-42478489979 / 1000000000000) (-42478489870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (190041632279229 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-21303894410 / 1000000000000) (-21303893448 / 1000000000000), orderedInterval (47226034308 / 1000000000000) (47226035270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (61455559227357 / 160000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40683510891 / 1000000000000) (40683511293 / 1000000000000), orderedInterval (-1567812901 / 1000000000000) (-1567812499 / 1000000000000)))) (orderedInterval (9828553220 / 1000000000000) (9828553354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (55453674328503 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79889209488 / 1000000000000) (79889209489 / 1000000000000), orderedInterval (52355692301 / 1000000000000) (52355692302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (148956369450891 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58383121593 / 1000000000000) (-58383121457 / 1000000000000), orderedInterval (3396036221 / 1000000000000) (3396036357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (404445519199647 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18415689861 / 1000000000000) (-18415689860 / 1000000000000), orderedInterval (-30315055714 / 1000000000000) (-30315055713 / 1000000000000)))) (orderedInterval (7718802817 / 1000000000000) (7718802958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (297912738901911 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25790239673 / 1000000000000) (25790246788 / 1000000000000), orderedInterval (-32351974236 / 1000000000000) (-32351967121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (510478555868403 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28701369968 / 1000000000000) (-28701369965 / 1000000000000), orderedInterval (-13165165170 / 1000000000000) (-13165165167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (376016193801177 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15459817878 / 1000000000000) (-15459817631 / 1000000000000), orderedInterval (33414744377 / 1000000000000) (33414744624 / 1000000000000)))) (orderedInterval (11916829955 / 1000000000000) (11916830172 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate451_chunkChecks4_1 :
    compactCertificate451.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (576905538194871 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17961520575 / 1000000000000) (-17961519817 / 1000000000000), orderedInterval (23680788791 / 1000000000000) (23680789548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (333076567773759 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25221353334 / 1000000000000) (25221360838 / 1000000000000), orderedInterval (-29912538382 / 1000000000000) (-29912530878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (591050214449931 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28462953124 / 1000000000000) (-28462953025 / 1000000000000), orderedInterval (-7159843827 / 1000000000000) (-7159843728 / 1000000000000)))) (orderedInterval (-26863450421 / 1000000000000) (-26863442341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (552235779356439 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2137461666 / 1000000000000) (-2137461665 / 1000000000000), orderedInterval (30294698019 / 1000000000000) (30294698020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (394101509766087 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6506039165 / 1000000000000) (-6506039164 / 1000000000000), orderedInterval (-35348284656 / 1000000000000) (-35348284655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (446869108352673 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5647184994 / 1000000000000) (5647184995 / 1000000000000), orderedInterval (33278690512 / 1000000000000) (33278690513 / 1000000000000)))) (orderedInterval (-2909348246 / 1000000000000) (-2909347941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (372552874097937 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36926795941 / 1000000000000) (36926796161 / 1000000000000), orderedInterval (1818846863 / 1000000000000) (1818847084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (329161762660677 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24997578595 / 1000000000000) (-24997578594 / 1000000000000), orderedInterval (-30340202905 / 1000000000000) (-30340202904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (95403908515023 / 160000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5109346948 / 1000000000000) (5109346949 / 1000000000000), orderedInterval (32268882577 / 1000000000000) (32268882578 / 1000000000000)))) (orderedInterval (7227922839 / 1000000000000) (7227923013 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate451_chunkChecks4_2 :
    compactCertificate451.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (263892231785181 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30991853069 / 1000000000000) (-30991853068 / 1000000000000), orderedInterval (-31088914524 / 1000000000000) (-31088914523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (223704367410741 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34679086626 / 1000000000000) (-34679086625 / 1000000000000), orderedInterval (-32710044776 / 1000000000000) (-32710044775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (139983806198823 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9892283421 / 1000000000000) (-9892283374 / 1000000000000), orderedInterval (59529568262 / 1000000000000) (59529568308 / 1000000000000)))) (orderedInterval (6547521874 / 1000000000000) (6547521943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (75283756538841 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49183833822 / 1000000000000) (49183833823 / 1000000000000), orderedInterval (65662833326 / 1000000000000) (65662833327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (204410043779523 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48267493602 / 1000000000000) (-48267491057 / 1000000000000), orderedInterval (12813928363 / 1000000000000) (12813930908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (279104439228771 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34716993579 / 1000000000000) (-34716993578 / 1000000000000), orderedInterval (-24839594953 / 1000000000000) (-24839594952 / 1000000000000)))) (orderedInterval (4082657924 / 1000000000000) (4082657985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (118016193801177 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-39752730282 / 1000000000000) (-39752730281 / 1000000000000), orderedInterval (-52164414966 / 1000000000000) (-52164414965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (479729275738617 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12765906619 / 1000000000000) (-12765906618 / 1000000000000), orderedInterval (-29967074268 / 1000000000000) (-29967074267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (320436923589303 / 800000000000) 4 (IntervalRat.scale (645 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28393061760 / 1000000000000) (-28393041809 / 1000000000000), orderedInterval (28021391450 / 1000000000000) (28021411401 / 1000000000000)))) (orderedInterval (25122218992 / 1000000000000) (25122228403 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate451_chunkChecks4 :
    compactCertificate451.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate451.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate451_chunkChecks4_0
    compactCertificate451_chunkChecks4_1 compactCertificate451_chunkChecks4_2

theorem compactCertificate451_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate451.chunkCheck r b = true :=
  compactCertificate451.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate451_chunkChecks0
    · exact compactCertificate451_chunkChecks1
    · exact compactCertificate451_chunkChecks2
    · exact compactCertificate451_chunkChecks3
    · exact compactCertificate451_chunkChecks4)

theorem compactCertificate451_coefficient0 :
    compactCertificate451.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate451_coefficient1 :
    compactCertificate451.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate451_coefficient2 :
    compactCertificate451.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate451_coefficient3 :
    compactCertificate451.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate451_coefficient4 :
    compactCertificate451.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate451_coefficients : ∀ r : Fin 5,
    compactCertificate451.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate451_coefficient0
  · exact compactCertificate451_coefficient1
  · exact compactCertificate451_coefficient2
  · exact compactCertificate451_coefficient3
  · exact compactCertificate451_coefficient4

theorem compactCertificate451_lower : (1 : ℚ) ≤ compactCertificate451.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate451, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate451_proves {t : ℝ} (ht : t ∈ compactCertificate451.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate451.proves compactCertificate451_states compactCertificate451_chunks
    compactCertificate451_coefficients compactCertificate451_lower ht

end Erdos232
