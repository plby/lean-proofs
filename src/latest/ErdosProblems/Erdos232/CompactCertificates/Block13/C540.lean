/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate540 : CompactCertificate where
  left := 411
  right := 412
  center := 823 / 2
  grid := fun i =>
    match i.val with
    | 0 => 131
    | 1 => 97
    | 2 => 156
    | 3 => 28
    | 4 => 76
    | 5 => 205
    | 6 => 151
    | 7 => 259
    | 8 => 191
    | 9 => 293
    | 10 => 169
    | 11 => 300
    | 12 => 281
    | 13 => 200
    | 14 => 227
    | 15 => 189
    | 16 => 167
    | 17 => 242
    | 18 => 134
    | 19 => 114
    | 20 => 71
    | 21 => 38
    | 22 => 104
    | 23 => 142
    | 24 => 60
    | 25 => 244
    | _ => 163
  point := fun i =>
    match i.val with
    | 0 => 823 / 2
    | 1 => 1212436150122523 / 4000000000000
    | 2 => 392076939876859 / 800000000000
    | 3 => 353785844746961 / 4000000000000
    | 4 => 950318543085917 / 4000000000000
    | 5 => 2580299707762089 / 4000000000000
    | 6 => 1900637086172657 / 4000000000000
    | 7 => 3256774042478261 / 4000000000000
    | 8 => 2398925019367199 / 4000000000000
    | 9 => 3680567890964177 / 4000000000000
    | 10 => 2124976862618633 / 4000000000000
    | 11 => 3770808732498397 / 4000000000000
    | 12 => 3523178654343793 / 4000000000000
    | 13 => 2514306531298369 / 4000000000000
    | 14 => 2850955629257751 / 4000000000000
    | 15 => 2376829576609319 / 4000000000000
    | 16 => 2100001012943699 / 4000000000000
    | 17 => 608662145022201 / 800000000000
    | 18 => 1683591525265147 / 4000000000000
    | 19 => 1427199181232867 / 4000000000000
    | 20 => 893074980632801 / 4000000000000
    | 21 => 480298694817567 / 4000000000000
    | 22 => 1304104387833701 / 4000000000000
    | 23 => 1780643050273477 / 4000000000000
    | 24 => 752925019367199 / 4000000000000
    | 25 => 3060598402580479 / 4000000000000
    | _ => 2044337892356561 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))
    | 1 => (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))
    | 2 => (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000))
    | 3 => (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))
    | 4 => (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))
    | 5 => (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000))
    | 6 => (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))
    | 7 => (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))
    | 8 => (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000))
    | 9 => (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))
    | 10 => (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))
    | 11 => (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000))
    | 12 => (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))
    | 13 => (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))
    | 14 => (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000))
    | 15 => (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))
    | 16 => (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))
    | 17 => (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000))
    | 18 => (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))
    | 19 => (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))
    | 20 => (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000))
    | 21 => (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))
    | 22 => (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))
    | 23 => (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000))
    | 24 => (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))
    | 25 => (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))
    | _ => (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8646657371 / 1000000000000) (-8646656890 / 1000000000000)
      | 1 => orderedInterval (548618312 / 1000000000000) (548619819 / 1000000000000)
      | 2 => orderedInterval (474287242 / 1000000000000) (474287269 / 1000000000000)
      | 3 => orderedInterval (2834831691 / 1000000000000) (2834831855 / 1000000000000)
      | 4 => orderedInterval (2203116443 / 1000000000000) (2203118155 / 1000000000000)
      | 5 => orderedInterval (2176046154 / 1000000000000) (2176046198 / 1000000000000)
      | 6 => orderedInterval (-4251296927 / 1000000000000) (-4251296698 / 1000000000000)
      | 7 => orderedInterval (-961845477 / 1000000000000) (-961845427 / 1000000000000)
      | _ => orderedInterval (146418055 / 1000000000000) (146418200 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9981578411 / 1000000000000) (-9981578045 / 1000000000000)
      | 1 => orderedInterval (36843720 / 1000000000000) (36846037 / 1000000000000)
      | 2 => orderedInterval (-576381350 / 1000000000000) (-576381302 / 1000000000000)
      | 3 => orderedInterval (12451750085 / 1000000000000) (12451750425 / 1000000000000)
      | 4 => orderedInterval (2923366725 / 1000000000000) (2923370362 / 1000000000000)
      | 5 => orderedInterval (1181983594 / 1000000000000) (1181983660 / 1000000000000)
      | 6 => orderedInterval (-7089315262 / 1000000000000) (-7089315057 / 1000000000000)
      | 7 => orderedInterval (-3921468749 / 1000000000000) (-3921468703 / 1000000000000)
      | _ => orderedInterval (4613768697 / 1000000000000) (4613768915 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8185946254 / 1000000000000) (8185946538 / 1000000000000)
      | 1 => orderedInterval (-5015820030 / 1000000000000) (-5015816416 / 1000000000000)
      | 2 => orderedInterval (-2496789874 / 1000000000000) (-2496789786 / 1000000000000)
      | 3 => orderedInterval (-22600911489 / 1000000000000) (-22600910760 / 1000000000000)
      | 4 => orderedInterval (-4165376277 / 1000000000000) (-4165368522 / 1000000000000)
      | 5 => orderedInterval (-4675187768 / 1000000000000) (-4675187668 / 1000000000000)
      | 6 => orderedInterval (3736714450 / 1000000000000) (3736714636 / 1000000000000)
      | 7 => orderedInterval (-364049776 / 1000000000000) (-364049731 / 1000000000000)
      | _ => orderedInterval (-2594189879 / 1000000000000) (-2594189537 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9126448565 / 1000000000000) (9126448790 / 1000000000000)
      | 1 => orderedInterval (1920851454 / 1000000000000) (1920857104 / 1000000000000)
      | 2 => orderedInterval (433150688 / 1000000000000) (433150849 / 1000000000000)
      | 3 => orderedInterval (-68315641699 / 1000000000000) (-68315640102 / 1000000000000)
      | 4 => orderedInterval (-7803975363 / 1000000000000) (-7803958823 / 1000000000000)
      | 5 => orderedInterval (-2371165216 / 1000000000000) (-2371165059 / 1000000000000)
      | 6 => orderedInterval (6507647263 / 1000000000000) (6507647434 / 1000000000000)
      | 7 => orderedInterval (4123332345 / 1000000000000) (4123332391 / 1000000000000)
      | _ => orderedInterval (-88115912 / 1000000000000) (-88115353 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-7390622370 / 1000000000000) (-7390622185 / 1000000000000)
      | 1 => orderedInterval (12931061892 / 1000000000000) (12931070754 / 1000000000000)
      | 2 => orderedInterval (11140378507 / 1000000000000) (11140378810 / 1000000000000)
      | 3 => orderedInterval (129959455511 / 1000000000000) (129959459057 / 1000000000000)
      | 4 => orderedInterval (5180374767 / 1000000000000) (5180410118 / 1000000000000)
      | 5 => orderedInterval (11698093759 / 1000000000000) (11698094015 / 1000000000000)
      | 6 => orderedInterval (-3878667851 / 1000000000000) (-3878667692 / 1000000000000)
      | 7 => orderedInterval (570001666 / 1000000000000) (570001715 / 1000000000000)
      | _ => orderedInterval (12889404947 / 1000000000000) (12889405896 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5476481878 / 1000000000000) (-5476477519 / 1000000000000)
    | 1 => orderedInterval (-361030951 / 1000000000000) (-361023708 / 1000000000000)
    | 2 => orderedInterval (-29989664389 / 1000000000000) (-29989651246 / 1000000000000)
    | 3 => orderedInterval (-56467467875 / 1000000000000) (-56467442769 / 1000000000000)
    | _ => orderedInterval (173099480828 / 1000000000000) (173099530488 / 1000000000000)

theorem compactCertificate540_stateChecks0 :
    compactCertificate540.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (823 / 2)) (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1212436150122523 / 4000000000000)) (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (392076939876859 / 800000000000)) (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks1 :
    compactCertificate540.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (353785844746961 / 4000000000000)) (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (950318543085917 / 4000000000000)) (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2580299707762089 / 4000000000000)) (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks2 :
    compactCertificate540.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1900637086172657 / 4000000000000)) (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3256774042478261 / 4000000000000)) (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2398925019367199 / 4000000000000)) (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks3 :
    compactCertificate540.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3680567890964177 / 4000000000000)) (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2124976862618633 / 4000000000000)) (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 300 12 (3770808732498397 / 4000000000000)) (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks4 :
    compactCertificate540.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3523178654343793 / 4000000000000)) (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2514306531298369 / 4000000000000)) (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2850955629257751 / 4000000000000)) (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks5 :
    compactCertificate540.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2376829576609319 / 4000000000000)) (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2100001012943699 / 4000000000000)) (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (608662145022201 / 800000000000)) (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks6 :
    compactCertificate540.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1683591525265147 / 4000000000000)) (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1427199181232867 / 4000000000000)) (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (893074980632801 / 4000000000000)) (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks7 :
    compactCertificate540.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (480298694817567 / 4000000000000)) (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1304104387833701 / 4000000000000)) (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1780643050273477 / 4000000000000)) (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_stateChecks8 :
    compactCertificate540.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (752925019367199 / 4000000000000)) (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3060598402580479 / 4000000000000)) (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2044337892356561 / 4000000000000)) (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_states : ∀ j,
    BesselStateValid (compactCertificate540.point j) (compactCertificate540.state j) :=
  compactCertificate540.statesValid_of_checks3 compactCertificate540_stateChecks0
    compactCertificate540_stateChecks1 compactCertificate540_stateChecks2
    compactCertificate540_stateChecks3 compactCertificate540_stateChecks4
    compactCertificate540_stateChecks5 compactCertificate540_stateChecks6
    compactCertificate540_stateChecks7 compactCertificate540_stateChecks8

theorem compactCertificate540_chunkChecks0_0 :
    compactCertificate540.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (823 / 2) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1212436150122523 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (392076939876859 / 800000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000)))) (orderedInterval (-8646657371 / 1000000000000) (-8646656890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (353785844746961 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (950318543085917 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2580299707762089 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000)))) (orderedInterval (548618312 / 1000000000000) (548619819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1900637086172657 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3256774042478261 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2398925019367199 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000)))) (orderedInterval (474287242 / 1000000000000) (474287269 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks0_1 :
    compactCertificate540.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3680567890964177 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2124976862618633 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3770808732498397 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000)))) (orderedInterval (2834831691 / 1000000000000) (2834831855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3523178654343793 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2514306531298369 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2850955629257751 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000)))) (orderedInterval (2203116443 / 1000000000000) (2203118155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2376829576609319 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2100001012943699 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (608662145022201 / 800000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000)))) (orderedInterval (2176046154 / 1000000000000) (2176046198 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks0_2 :
    compactCertificate540.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1683591525265147 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1427199181232867 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (893074980632801 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000)))) (orderedInterval (-4251296927 / 1000000000000) (-4251296698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (480298694817567 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1304104387833701 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1780643050273477 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000)))) (orderedInterval (-961845477 / 1000000000000) (-961845427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (752925019367199 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3060598402580479 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2044337892356561 / 4000000000000) 0 (IntervalRat.scale (823 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000)))) (orderedInterval (146418055 / 1000000000000) (146418200 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks0 :
    compactCertificate540.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate540.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate540_chunkChecks0_0
    compactCertificate540_chunkChecks0_1 compactCertificate540_chunkChecks0_2

theorem compactCertificate540_chunkChecks1_0 :
    compactCertificate540.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (823 / 2) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1212436150122523 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (392076939876859 / 800000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000)))) (orderedInterval (-9981578411 / 1000000000000) (-9981578045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (353785844746961 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (950318543085917 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2580299707762089 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000)))) (orderedInterval (36843720 / 1000000000000) (36846037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1900637086172657 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3256774042478261 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2398925019367199 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000)))) (orderedInterval (-576381350 / 1000000000000) (-576381302 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks1_1 :
    compactCertificate540.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3680567890964177 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2124976862618633 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3770808732498397 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000)))) (orderedInterval (12451750085 / 1000000000000) (12451750425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3523178654343793 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2514306531298369 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2850955629257751 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000)))) (orderedInterval (2923366725 / 1000000000000) (2923370362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2376829576609319 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2100001012943699 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (608662145022201 / 800000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000)))) (orderedInterval (1181983594 / 1000000000000) (1181983660 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks1_2 :
    compactCertificate540.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1683591525265147 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1427199181232867 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (893074980632801 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000)))) (orderedInterval (-7089315262 / 1000000000000) (-7089315057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (480298694817567 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1304104387833701 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1780643050273477 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000)))) (orderedInterval (-3921468749 / 1000000000000) (-3921468703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (752925019367199 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3060598402580479 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2044337892356561 / 4000000000000) 1 (IntervalRat.scale (823 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000)))) (orderedInterval (4613768697 / 1000000000000) (4613768915 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks1 :
    compactCertificate540.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate540.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate540_chunkChecks1_0
    compactCertificate540_chunkChecks1_1 compactCertificate540_chunkChecks1_2

theorem compactCertificate540_chunkChecks2_0 :
    compactCertificate540.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (823 / 2) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1212436150122523 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (392076939876859 / 800000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000)))) (orderedInterval (8185946254 / 1000000000000) (8185946538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (353785844746961 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (950318543085917 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2580299707762089 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000)))) (orderedInterval (-5015820030 / 1000000000000) (-5015816416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1900637086172657 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3256774042478261 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2398925019367199 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000)))) (orderedInterval (-2496789874 / 1000000000000) (-2496789786 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks2_1 :
    compactCertificate540.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3680567890964177 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2124976862618633 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3770808732498397 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000)))) (orderedInterval (-22600911489 / 1000000000000) (-22600910760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3523178654343793 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2514306531298369 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2850955629257751 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000)))) (orderedInterval (-4165376277 / 1000000000000) (-4165368522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2376829576609319 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2100001012943699 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (608662145022201 / 800000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000)))) (orderedInterval (-4675187768 / 1000000000000) (-4675187668 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks2_2 :
    compactCertificate540.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1683591525265147 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1427199181232867 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (893074980632801 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000)))) (orderedInterval (3736714450 / 1000000000000) (3736714636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (480298694817567 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1304104387833701 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1780643050273477 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000)))) (orderedInterval (-364049776 / 1000000000000) (-364049731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (752925019367199 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3060598402580479 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2044337892356561 / 4000000000000) 2 (IntervalRat.scale (823 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000)))) (orderedInterval (-2594189879 / 1000000000000) (-2594189537 / 1000000000000))) = true
  rfl'

theorem compactCertificate540_chunkChecks2 :
    compactCertificate540.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate540.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate540_chunkChecks2_0
    compactCertificate540_chunkChecks2_1 compactCertificate540_chunkChecks2_2

theorem compactCertificate540_chunkChecks3_0 :
    compactCertificate540.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (823 / 2) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1212436150122523 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (392076939876859 / 800000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000)))) (orderedInterval (9126448565 / 1000000000000) (9126448790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (353785844746961 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (950318543085917 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2580299707762089 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000)))) (orderedInterval (1920851454 / 1000000000000) (1920857104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1900637086172657 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3256774042478261 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2398925019367199 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000)))) (orderedInterval (433150688 / 1000000000000) (433150849 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate540_chunkChecks3_1 :
    compactCertificate540.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3680567890964177 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2124976862618633 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3770808732498397 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000)))) (orderedInterval (-68315641699 / 1000000000000) (-68315640102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3523178654343793 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2514306531298369 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2850955629257751 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000)))) (orderedInterval (-7803975363 / 1000000000000) (-7803958823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2376829576609319 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2100001012943699 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (608662145022201 / 800000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000)))) (orderedInterval (-2371165216 / 1000000000000) (-2371165059 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate540_chunkChecks3_2 :
    compactCertificate540.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1683591525265147 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1427199181232867 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (893074980632801 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000)))) (orderedInterval (6507647263 / 1000000000000) (6507647434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (480298694817567 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1304104387833701 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1780643050273477 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000)))) (orderedInterval (4123332345 / 1000000000000) (4123332391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (752925019367199 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3060598402580479 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2044337892356561 / 4000000000000) 3 (IntervalRat.scale (823 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000)))) (orderedInterval (-88115912 / 1000000000000) (-88115353 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate540_chunkChecks3 :
    compactCertificate540.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate540.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate540_chunkChecks3_0
    compactCertificate540_chunkChecks3_1 compactCertificate540_chunkChecks3_2

theorem compactCertificate540_chunkChecks4_0 :
    compactCertificate540.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (823 / 2) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26418555886 / 1000000000000) (-26418555885 / 1000000000000), orderedInterval (-29107754786 / 1000000000000) (-29107754785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1212436150122523 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34140412419 / 1000000000000) (34140460901 / 1000000000000), orderedInterval (-30629690880 / 1000000000000) (-30629642398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (392076939876859 / 800000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25674534460 / 1000000000000) (25674534461 / 1000000000000), orderedInterval (25267824532 / 1000000000000) (25267824533 / 1000000000000)))) (orderedInterval (-7390622370 / 1000000000000) (-7390622185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (353785844746961 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (80924989248 / 1000000000000) (80924989249 / 1000000000000), orderedInterval (25015068390 / 1000000000000) (25015068391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (950318543085917 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19992802267 / 1000000000000) (-19992801578 / 1000000000000), orderedInterval (47790351287 / 1000000000000) (47790351976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2580299707762089 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30335933826 / 1000000000000) (-30335913670 / 1000000000000), orderedInterval (8185868914 / 1000000000000) (8185889070 / 1000000000000)))) (orderedInterval (12931061892 / 1000000000000) (12931070754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1900637086172657 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36602441902 / 1000000000000) (-36602441489 / 1000000000000), orderedInterval (-213327154 / 1000000000000) (-213326741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3256774042478261 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26989789953 / 1000000000000) (-26989789821 / 1000000000000), orderedInterval (-7294609200 / 1000000000000) (-7294609068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2398925019367199 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14820649234 / 1000000000000) (-14820649233 / 1000000000000), orderedInterval (-29002415779 / 1000000000000) (-29002415778 / 1000000000000)))) (orderedInterval (11140378507 / 1000000000000) (11140378810 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate540_chunkChecks4_1 :
    compactCertificate540.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3680567890964177 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11217655406 / 1000000000000) (-11217655405 / 1000000000000), orderedInterval (-23785405338 / 1000000000000) (-23785405337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2124976862618633 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30854623619 / 1000000000000) (-30854623617 / 1000000000000), orderedInterval (-15666438321 / 1000000000000) (-15666438319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3770808732498397 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22001645604 / 1000000000000) (22001645608 / 1000000000000), orderedInterval (13817333652 / 1000000000000) (13817333656 / 1000000000000)))) (orderedInterval (129959455511 / 1000000000000) (129959459057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3523178654343793 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25130864076 / 1000000000000) (25130956132 / 1000000000000), orderedInterval (-9565022800 / 1000000000000) (-9564930743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2514306531298369 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27498574925 / 1000000000000) (27498574926 / 1000000000000), orderedInterval (15997614987 / 1000000000000) (15997614988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2850955629257751 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11157568729 / 1000000000000) (-11157568728 / 1000000000000), orderedInterval (-27717806298 / 1000000000000) (-27717806297 / 1000000000000)))) (orderedInterval (5180374767 / 1000000000000) (5180410118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2376829576609319 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30866573712 / 1000000000000) (-30866573703 / 1000000000000), orderedInterval (-10865800234 / 1000000000000) (-10865800226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2100001012943699 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31632762775 / 1000000000000) (-31632762774 / 1000000000000), orderedInterval (-14529285228 / 1000000000000) (-14529285226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (608662145022201 / 800000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28208353930 / 1000000000000) (28208354091 / 1000000000000), orderedInterval (6387313530 / 1000000000000) (6387313691 / 1000000000000)))) (orderedInterval (11698093759 / 1000000000000) (11698094015 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate540_chunkChecks4_2 :
    compactCertificate540.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1683591525265147 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25337833317 / 1000000000000) (25337833318 / 1000000000000), orderedInterval (29474513934 / 1000000000000) (29474513935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1427199181232867 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22319965362 / 1000000000000) (-22319963145 / 1000000000000), orderedInterval (35893084230 / 1000000000000) (35893086447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (893074980632801 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44947491390 / 1000000000000) (-44947491389 / 1000000000000), orderedInterval (-28727817251 / 1000000000000) (-28727817250 / 1000000000000)))) (orderedInterval (-3878667851 / 1000000000000) (-3878667692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (480298694817567 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72503746764 / 1000000000000) (72503746773 / 1000000000000), orderedInterval (6408313591 / 1000000000000) (6408313600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1304104387833701 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (3772485321 / 1000000000000) (3772485322 / 1000000000000), orderedInterval (44021884053 / 1000000000000) (44021884054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1780643050273477 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-6035195570 / 1000000000000) (-6035195565 / 1000000000000), orderedInterval (37338626462 / 1000000000000) (37338626468 / 1000000000000)))) (orderedInterval (570001666 / 1000000000000) (570001715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (752925019367199 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28918172938 / 1000000000000) (28918172939 / 1000000000000), orderedInterval (50379705104 / 1000000000000) (50379705105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3060598402580479 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16613283771 / 1000000000000) (-16613283402 / 1000000000000), orderedInterval (23590908422 / 1000000000000) (23590908790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2044337892356561 / 4000000000000) 4 (IntervalRat.scale (823 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7356427321 / 1000000000000) (7356427328 / 1000000000000), orderedInterval (-34525436473 / 1000000000000) (-34525436466 / 1000000000000)))) (orderedInterval (12889404947 / 1000000000000) (12889405896 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate540_chunkChecks4 :
    compactCertificate540.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate540.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate540_chunkChecks4_0
    compactCertificate540_chunkChecks4_1 compactCertificate540_chunkChecks4_2

theorem compactCertificate540_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate540.chunkCheck r b = true :=
  compactCertificate540.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate540_chunkChecks0
    · exact compactCertificate540_chunkChecks1
    · exact compactCertificate540_chunkChecks2
    · exact compactCertificate540_chunkChecks3
    · exact compactCertificate540_chunkChecks4)

theorem compactCertificate540_coefficient0 :
    compactCertificate540.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate540_coefficient1 :
    compactCertificate540.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate540_coefficient2 :
    compactCertificate540.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate540_coefficient3 :
    compactCertificate540.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate540_coefficient4 :
    compactCertificate540.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate540_coefficients : ∀ r : Fin 5,
    compactCertificate540.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate540_coefficient0
  · exact compactCertificate540_coefficient1
  · exact compactCertificate540_coefficient2
  · exact compactCertificate540_coefficient3
  · exact compactCertificate540_coefficient4

theorem compactCertificate540_lower : (1 : ℚ) ≤ compactCertificate540.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate540, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate540_proves {t : ℝ} (ht : t ∈ compactCertificate540.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate540.proves compactCertificate540_states compactCertificate540_chunks
    compactCertificate540_coefficients compactCertificate540_lower ht

end Erdos232
