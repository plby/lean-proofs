/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate477 : CompactCertificate where
  left := 348
  right := 349
  center := 697 / 2
  grid := fun i =>
    match i.val with
    | 0 => 111
    | 1 => 82
    | 2 => 132
    | 3 => 24
    | 4 => 64
    | 5 => 174
    | 6 => 128
    | 7 => 220
    | 8 => 162
    | 9 => 248
    | 10 => 143
    | 11 => 254
    | 12 => 238
    | 13 => 170
    | 14 => 192
    | 15 => 160
    | 16 => 142
    | 17 => 205
    | 18 => 114
    | 19 => 96
    | 20 => 60
    | 21 => 32
    | 22 => 88
    | 23 => 120
    | 24 => 51
    | 25 => 206
    | _ => 138
  point := fun i =>
    match i.val with
    | 0 => 697 / 2
    | 1 => 1026814090686997 / 4000000000000
    | 2 => 332050579701301 / 800000000000
    | 3 => 299621790751679 / 4000000000000
    | 4 => 804826275250163 / 4000000000000
    | 5 => 2185259898311271 / 4000000000000
    | 6 => 1609652550501023 / 4000000000000
    | 7 => 2758167080932379 / 4000000000000
    | 8 => 2031653388212561 / 4000000000000
    | 9 => 3117078760634303 / 4000000000000
    | 10 => 1799646261537287 / 4000000000000
    | 11 => 3193503871872883 / 4000000000000
    | 12 => 2983785567530527 / 4000000000000
    | 13 => 2129370172922191 / 4000000000000
    | 14 => 2414478825750489 / 4000000000000
    | 15 => 2012940722839241 / 4000000000000
    | 16 => 1778494174996061 / 4000000000000
    | 17 => 515476932054039 / 800000000000
    | 18 => 1425836322126133 / 4000000000000
    | 19 => 1208697240971213 / 4000000000000
    | 20 => 756346611787439 / 4000000000000
    | 21 => 406765723314513 / 4000000000000
    | 22 => 1104448066002539 / 4000000000000
    | 23 => 1508029411957003 / 4000000000000
    | 24 => 637653388212561 / 4000000000000
    | 25 => 2592025621626481 / 4000000000000
    | _ => 1731352990246079 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))
    | 1 => (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))
    | 2 => (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000))
    | 3 => (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))
    | 4 => (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))
    | 5 => (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000))
    | 6 => (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))
    | 7 => (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))
    | 8 => (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000))
    | 9 => (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))
    | 10 => (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))
    | 11 => (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000))
    | 12 => (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))
    | 13 => (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))
    | 14 => (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000))
    | 15 => (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))
    | 16 => (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))
    | 17 => (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000))
    | 18 => (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))
    | 19 => (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))
    | 20 => (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000))
    | 21 => (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))
    | 22 => (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))
    | 23 => (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000))
    | 24 => (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))
    | 25 => (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))
    | _ => (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7068229323 / 1000000000000) (-7068229298 / 1000000000000)
      | 1 => orderedInterval (274786372 / 1000000000000) (274786415 / 1000000000000)
      | 2 => orderedInterval (484415592 / 1000000000000) (484415809 / 1000000000000)
      | 3 => orderedInterval (-3131047531 / 1000000000000) (-3131047383 / 1000000000000)
      | 4 => orderedInterval (-2366693883 / 1000000000000) (-2366689415 / 1000000000000)
      | 5 => orderedInterval (1073935003 / 1000000000000) (1073935395 / 1000000000000)
      | 6 => orderedInterval (4591606764 / 1000000000000) (4591616927 / 1000000000000)
      | 7 => orderedInterval (-4082959375 / 1000000000000) (-4082959261 / 1000000000000)
      | _ => orderedInterval (-3139673633 / 1000000000000) (-3139673342 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12831191199 / 1000000000000) (-12831191170 / 1000000000000)
      | 1 => orderedInterval (-2900563713 / 1000000000000) (-2900563665 / 1000000000000)
      | 2 => orderedInterval (-49727128 / 1000000000000) (-49726705 / 1000000000000)
      | 3 => orderedInterval (-3770419875 / 1000000000000) (-3770419573 / 1000000000000)
      | 4 => orderedInterval (2198612372 / 1000000000000) (2198619421 / 1000000000000)
      | 5 => orderedInterval (-2666590940 / 1000000000000) (-2666590435 / 1000000000000)
      | 6 => orderedInterval (-4575367020 / 1000000000000) (-4575356634 / 1000000000000)
      | 7 => orderedInterval (-2990942704 / 1000000000000) (-2990942644 / 1000000000000)
      | _ => orderedInterval (-8825540465 / 1000000000000) (-8825539969 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6198195069 / 1000000000000) (6198195102 / 1000000000000)
      | 1 => orderedInterval (2136684698 / 1000000000000) (2136684764 / 1000000000000)
      | 2 => orderedInterval (-2259761391 / 1000000000000) (-2259760560 / 1000000000000)
      | 3 => orderedInterval (5517383632 / 1000000000000) (5517384273 / 1000000000000)
      | 4 => orderedInterval (4642493604 / 1000000000000) (4642504871 / 1000000000000)
      | 5 => orderedInterval (-636762229 / 1000000000000) (-636761572 / 1000000000000)
      | 6 => orderedInterval (-4146220616 / 1000000000000) (-4146209968 / 1000000000000)
      | 7 => orderedInterval (3060900063 / 1000000000000) (3060900107 / 1000000000000)
      | _ => orderedInterval (9759147902 / 1000000000000) (9759148773 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12510369907 / 1000000000000) (12510369944 / 1000000000000)
      | 1 => orderedInterval (8128069309 / 1000000000000) (8128069408 / 1000000000000)
      | 2 => orderedInterval (2371045977 / 1000000000000) (2371047610 / 1000000000000)
      | 3 => orderedInterval (16558767100 / 1000000000000) (16558768499 / 1000000000000)
      | 4 => orderedInterval (-3636737201 / 1000000000000) (-3636718962 / 1000000000000)
      | 5 => orderedInterval (5482463775 / 1000000000000) (5482464632 / 1000000000000)
      | 6 => orderedInterval (4812343822 / 1000000000000) (4812354709 / 1000000000000)
      | 7 => orderedInterval (3238568978 / 1000000000000) (3238569019 / 1000000000000)
      | _ => orderedInterval (12867883923 / 1000000000000) (12867885478 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4969425890 / 1000000000000) (-4969425846 / 1000000000000)
      | 1 => orderedInterval (-6410113336 / 1000000000000) (-6410113183 / 1000000000000)
      | 2 => orderedInterval (9605646096 / 1000000000000) (9605649318 / 1000000000000)
      | 3 => orderedInterval (-7391974883 / 1000000000000) (-7391971783 / 1000000000000)
      | 4 => orderedInterval (-6661820968 / 1000000000000) (-6661790852 / 1000000000000)
      | 5 => orderedInterval (-3000593365 / 1000000000000) (-3000592235 / 1000000000000)
      | 6 => orderedInterval (4476694645 / 1000000000000) (4476705808 / 1000000000000)
      | 7 => orderedInterval (-3308037623 / 1000000000000) (-3308037581 / 1000000000000)
      | _ => orderedInterval (-31959582903 / 1000000000000) (-31959580086 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13363860014 / 1000000000000) (-13363844153 / 1000000000000)
    | 1 => orderedInterval (-36411730672 / 1000000000000) (-36411711374 / 1000000000000)
    | 2 => orderedInterval (24272060732 / 1000000000000) (24272085790 / 1000000000000)
    | 3 => orderedInterval (62332775590 / 1000000000000) (62332810337 / 1000000000000)
    | _ => orderedInterval (-49619208227 / 1000000000000) (-49619156440 / 1000000000000)

theorem compactCertificate477_stateChecks0 :
    compactCertificate477.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (697 / 2)) (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1026814090686997 / 4000000000000)) (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (332050579701301 / 800000000000)) (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks1 :
    compactCertificate477.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (299621790751679 / 4000000000000)) (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (804826275250163 / 4000000000000)) (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2185259898311271 / 4000000000000)) (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks2 :
    compactCertificate477.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1609652550501023 / 4000000000000)) (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2758167080932379 / 4000000000000)) (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2031653388212561 / 4000000000000)) (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks3 :
    compactCertificate477.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3117078760634303 / 4000000000000)) (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1799646261537287 / 4000000000000)) (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (3193503871872883 / 4000000000000)) (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks4 :
    compactCertificate477.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2983785567530527 / 4000000000000)) (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2129370172922191 / 4000000000000)) (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2414478825750489 / 4000000000000)) (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks5 :
    compactCertificate477.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2012940722839241 / 4000000000000)) (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1778494174996061 / 4000000000000)) (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (515476932054039 / 800000000000)) (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks6 :
    compactCertificate477.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1425836322126133 / 4000000000000)) (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1208697240971213 / 4000000000000)) (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (756346611787439 / 4000000000000)) (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks7 :
    compactCertificate477.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (406765723314513 / 4000000000000)) (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104448066002539 / 4000000000000)) (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1508029411957003 / 4000000000000)) (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_stateChecks8 :
    compactCertificate477.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (637653388212561 / 4000000000000)) (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2592025621626481 / 4000000000000)) (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1731352990246079 / 4000000000000)) (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_states : ∀ j,
    BesselStateValid (compactCertificate477.point j) (compactCertificate477.state j) :=
  compactCertificate477.statesValid_of_checks3 compactCertificate477_stateChecks0
    compactCertificate477_stateChecks1 compactCertificate477_stateChecks2
    compactCertificate477_stateChecks3 compactCertificate477_stateChecks4
    compactCertificate477_stateChecks5 compactCertificate477_stateChecks6
    compactCertificate477_stateChecks7 compactCertificate477_stateChecks8

theorem compactCertificate477_chunkChecks0_0 :
    compactCertificate477.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (697 / 2) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1026814090686997 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (332050579701301 / 800000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000)))) (orderedInterval (-7068229323 / 1000000000000) (-7068229298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (299621790751679 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (804826275250163 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2185259898311271 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000)))) (orderedInterval (274786372 / 1000000000000) (274786415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1609652550501023 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2758167080932379 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2031653388212561 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000)))) (orderedInterval (484415592 / 1000000000000) (484415809 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks0_1 :
    compactCertificate477.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3117078760634303 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1799646261537287 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3193503871872883 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000)))) (orderedInterval (-3131047531 / 1000000000000) (-3131047383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2983785567530527 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2129370172922191 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2414478825750489 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000)))) (orderedInterval (-2366693883 / 1000000000000) (-2366689415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2012940722839241 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1778494174996061 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (515476932054039 / 800000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000)))) (orderedInterval (1073935003 / 1000000000000) (1073935395 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks0_2 :
    compactCertificate477.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1425836322126133 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1208697240971213 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (756346611787439 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000)))) (orderedInterval (4591606764 / 1000000000000) (4591616927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (406765723314513 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1104448066002539 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1508029411957003 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000)))) (orderedInterval (-4082959375 / 1000000000000) (-4082959261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (637653388212561 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2592025621626481 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1731352990246079 / 4000000000000) 0 (IntervalRat.scale (697 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000)))) (orderedInterval (-3139673633 / 1000000000000) (-3139673342 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks0 :
    compactCertificate477.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate477.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate477_chunkChecks0_0
    compactCertificate477_chunkChecks0_1 compactCertificate477_chunkChecks0_2

theorem compactCertificate477_chunkChecks1_0 :
    compactCertificate477.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (697 / 2) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1026814090686997 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (332050579701301 / 800000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000)))) (orderedInterval (-12831191199 / 1000000000000) (-12831191170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (299621790751679 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (804826275250163 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2185259898311271 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000)))) (orderedInterval (-2900563713 / 1000000000000) (-2900563665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1609652550501023 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2758167080932379 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2031653388212561 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000)))) (orderedInterval (-49727128 / 1000000000000) (-49726705 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks1_1 :
    compactCertificate477.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3117078760634303 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1799646261537287 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3193503871872883 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000)))) (orderedInterval (-3770419875 / 1000000000000) (-3770419573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2983785567530527 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2129370172922191 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2414478825750489 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000)))) (orderedInterval (2198612372 / 1000000000000) (2198619421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2012940722839241 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1778494174996061 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (515476932054039 / 800000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000)))) (orderedInterval (-2666590940 / 1000000000000) (-2666590435 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks1_2 :
    compactCertificate477.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1425836322126133 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1208697240971213 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (756346611787439 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000)))) (orderedInterval (-4575367020 / 1000000000000) (-4575356634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (406765723314513 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1104448066002539 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1508029411957003 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000)))) (orderedInterval (-2990942704 / 1000000000000) (-2990942644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (637653388212561 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2592025621626481 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1731352990246079 / 4000000000000) 1 (IntervalRat.scale (697 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000)))) (orderedInterval (-8825540465 / 1000000000000) (-8825539969 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks1 :
    compactCertificate477.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate477.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate477_chunkChecks1_0
    compactCertificate477_chunkChecks1_1 compactCertificate477_chunkChecks1_2

theorem compactCertificate477_chunkChecks2_0 :
    compactCertificate477.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (697 / 2) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1026814090686997 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (332050579701301 / 800000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000)))) (orderedInterval (6198195069 / 1000000000000) (6198195102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (299621790751679 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (804826275250163 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2185259898311271 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000)))) (orderedInterval (2136684698 / 1000000000000) (2136684764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1609652550501023 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2758167080932379 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2031653388212561 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000)))) (orderedInterval (-2259761391 / 1000000000000) (-2259760560 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks2_1 :
    compactCertificate477.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3117078760634303 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1799646261537287 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3193503871872883 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000)))) (orderedInterval (5517383632 / 1000000000000) (5517384273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2983785567530527 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2129370172922191 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2414478825750489 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000)))) (orderedInterval (4642493604 / 1000000000000) (4642504871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2012940722839241 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1778494174996061 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (515476932054039 / 800000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000)))) (orderedInterval (-636762229 / 1000000000000) (-636761572 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks2_2 :
    compactCertificate477.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1425836322126133 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1208697240971213 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (756346611787439 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000)))) (orderedInterval (-4146220616 / 1000000000000) (-4146209968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (406765723314513 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1104448066002539 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1508029411957003 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000)))) (orderedInterval (3060900063 / 1000000000000) (3060900107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (637653388212561 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2592025621626481 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1731352990246079 / 4000000000000) 2 (IntervalRat.scale (697 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000)))) (orderedInterval (9759147902 / 1000000000000) (9759148773 / 1000000000000))) = true
  rfl'

theorem compactCertificate477_chunkChecks2 :
    compactCertificate477.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate477.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate477_chunkChecks2_0
    compactCertificate477_chunkChecks2_1 compactCertificate477_chunkChecks2_2

theorem compactCertificate477_chunkChecks3_0 :
    compactCertificate477.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (697 / 2) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1026814090686997 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (332050579701301 / 800000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000)))) (orderedInterval (12510369907 / 1000000000000) (12510369944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (299621790751679 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (804826275250163 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2185259898311271 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000)))) (orderedInterval (8128069309 / 1000000000000) (8128069408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1609652550501023 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2758167080932379 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2031653388212561 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000)))) (orderedInterval (2371045977 / 1000000000000) (2371047610 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate477_chunkChecks3_1 :
    compactCertificate477.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3117078760634303 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1799646261537287 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3193503871872883 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000)))) (orderedInterval (16558767100 / 1000000000000) (16558768499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2983785567530527 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2129370172922191 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2414478825750489 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000)))) (orderedInterval (-3636737201 / 1000000000000) (-3636718962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2012940722839241 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1778494174996061 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (515476932054039 / 800000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000)))) (orderedInterval (5482463775 / 1000000000000) (5482464632 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate477_chunkChecks3_2 :
    compactCertificate477.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1425836322126133 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1208697240971213 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (756346611787439 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000)))) (orderedInterval (4812343822 / 1000000000000) (4812354709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (406765723314513 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1104448066002539 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1508029411957003 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000)))) (orderedInterval (3238568978 / 1000000000000) (3238569019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (637653388212561 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2592025621626481 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1731352990246079 / 4000000000000) 3 (IntervalRat.scale (697 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000)))) (orderedInterval (12867883923 / 1000000000000) (12867885478 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate477_chunkChecks3 :
    compactCertificate477.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate477.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate477_chunkChecks3_0
    compactCertificate477_chunkChecks3_1 compactCertificate477_chunkChecks3_2

theorem compactCertificate477_chunkChecks4_0 :
    compactCertificate477.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (697 / 2) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23001254406 / 1000000000000) (-23001254405 / 1000000000000), orderedInterval (-35990403467 / 1000000000000) (-35990403466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1026814090686997 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6068552833 / 1000000000000) (-6068552820 / 1000000000000), orderedInterval (49440130762 / 1000000000000) (49440130775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (332050579701301 / 800000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35875408531 / 1000000000000) (35875408532 / 1000000000000), orderedInterval (15664876245 / 1000000000000) (15664876246 / 1000000000000)))) (orderedInterval (-4969425890 / 1000000000000) (-4969425846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (299621790751679 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (26445838438 / 1000000000000) (26445838439 / 1000000000000), orderedInterval (88139695890 / 1000000000000) (88139695891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (804826275250163 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45071034589 / 1000000000000) (45071034590 / 1000000000000), orderedInterval (33542269602 / 1000000000000) (33542269603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2185259898311271 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15247188777 / 1000000000000) (15247188778 / 1000000000000), orderedInterval (30528173285 / 1000000000000) (30528173286 / 1000000000000)))) (orderedInterval (-6410113336 / 1000000000000) (-6410113183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1609652550501023 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34973172145 / 1000000000000) (34973172146 / 1000000000000), orderedInterval (18900726966 / 1000000000000) (18900726967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2758167080932379 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22286175780 / 1000000000000) (-22286169417 / 1000000000000), orderedInterval (20669896798 / 1000000000000) (20669903161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2031653388212561 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8398659497 / 1000000000000) (-8398659486 / 1000000000000), orderedInterval (34401077903 / 1000000000000) (34401077914 / 1000000000000)))) (orderedInterval (9605646096 / 1000000000000) (9605649318 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate477_chunkChecks4_1 :
    compactCertificate477.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3117078760634303 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23080966304 / 1000000000000) (23080966305 / 1000000000000), orderedInterval (16843809780 / 1000000000000) (16843809781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1799646261537287 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37337370269 / 1000000000000) (-37337370196 / 1000000000000), orderedInterval (-4531100073 / 1000000000000) (-4531100000 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3193503871872883 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26284900375 / 1000000000000) (26284900399 / 1000000000000), orderedInterval (10303293993 / 1000000000000) (10303294017 / 1000000000000)))) (orderedInterval (-7391974883 / 1000000000000) (-7391971783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2983785567530527 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24055416416 / 1000000000000) (-24055396509 / 1000000000000), orderedInterval (16592494163 / 1000000000000) (16592514069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2129370172922191 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27988592688 / 1000000000000) (-27988549684 / 1000000000000), orderedInterval (20336938011 / 1000000000000) (20336981015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2414478825750489 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30487925540 / 1000000000000) (30487925547 / 1000000000000), orderedInterval (11162078451 / 1000000000000) (11162078458 / 1000000000000)))) (orderedInterval (-6661820968 / 1000000000000) (-6661790852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2012940722839241 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34820736873 / 1000000000000) (34820736905 / 1000000000000), orderedInterval (7215913246 / 1000000000000) (7215913278 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1778494174996061 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24304239201 / 1000000000000) (-24304232953 / 1000000000000), orderedInterval (29029427366 / 1000000000000) (29029433614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (515476932054039 / 800000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28082145445 / 1000000000000) (-28082145443 / 1000000000000), orderedInterval (-14099181561 / 1000000000000) (-14099181559 / 1000000000000)))) (orderedInterval (-3000593365 / 1000000000000) (-3000592235 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate477_chunkChecks4_2 :
    compactCertificate477.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1425836322126133 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33036341979 / 1000000000000) (-33036278970 / 1000000000000), orderedInterval (26400745831 / 1000000000000) (26400808840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1208697240971213 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44944356513 / 1000000000000) (44944356520 / 1000000000000), orderedInterval (9242211151 / 1000000000000) (9242211158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (756346611787439 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56924855267 / 1000000000000) (56924855270 / 1000000000000), orderedInterval (11090690823 / 1000000000000) (11090690827 / 1000000000000)))) (orderedInterval (4476694645 / 1000000000000) (4476705808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (406765723314513 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73656890933 / 1000000000000) (73656894822 / 1000000000000), orderedInterval (-29257057421 / 1000000000000) (-29257053532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1104448066002539 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20313673693 / 1000000000000) (20313673694 / 1000000000000), orderedInterval (43472003676 / 1000000000000) (43472003677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1508029411957003 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29515344651 / 1000000000000) (29515344652 / 1000000000000), orderedInterval (28552079279 / 1000000000000) (28552079280 / 1000000000000)))) (orderedInterval (-3308037623 / 1000000000000) (-3308037581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (637653388212561 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (1470029587 / 1000000000000) (1470029593 / 1000000000000), orderedInterval (-63181938611 / 1000000000000) (-63181938605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2592025621626481 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31300143991 / 1000000000000) (31300146368 / 1000000000000), orderedInterval (-1676068741 / 1000000000000) (-1676066365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1731352990246079 / 4000000000000) 4 (IntervalRat.scale (697 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3201295040 / 1000000000000) (3201295042 / 1000000000000), orderedInterval (38213518385 / 1000000000000) (38213518386 / 1000000000000)))) (orderedInterval (-31959582903 / 1000000000000) (-31959580086 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate477_chunkChecks4 :
    compactCertificate477.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate477.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate477_chunkChecks4_0
    compactCertificate477_chunkChecks4_1 compactCertificate477_chunkChecks4_2

theorem compactCertificate477_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate477.chunkCheck r b = true :=
  compactCertificate477.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate477_chunkChecks0
    · exact compactCertificate477_chunkChecks1
    · exact compactCertificate477_chunkChecks2
    · exact compactCertificate477_chunkChecks3
    · exact compactCertificate477_chunkChecks4)

theorem compactCertificate477_coefficient0 :
    compactCertificate477.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate477_coefficient1 :
    compactCertificate477.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate477_coefficient2 :
    compactCertificate477.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate477_coefficient3 :
    compactCertificate477.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate477_coefficient4 :
    compactCertificate477.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate477_coefficients : ∀ r : Fin 5,
    compactCertificate477.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate477_coefficient0
  · exact compactCertificate477_coefficient1
  · exact compactCertificate477_coefficient2
  · exact compactCertificate477_coefficient3
  · exact compactCertificate477_coefficient4

theorem compactCertificate477_lower : (1 : ℚ) ≤ compactCertificate477.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate477, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate477_proves {t : ℝ} (ht : t ∈ compactCertificate477.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate477.proves compactCertificate477_states compactCertificate477_chunks
    compactCertificate477_coefficients compactCertificate477_lower ht

end Erdos232
