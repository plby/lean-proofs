/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate411 : CompactCertificate where
  left := 282
  right := 283
  center := 565 / 2
  grid := fun i =>
    match i.val with
    | 0 => 90
    | 1 => 66
    | 2 => 107
    | 3 => 19
    | 4 => 52
    | 5 => 141
    | 6 => 104
    | 7 => 178
    | 8 => 131
    | 9 => 201
    | 10 => 116
    | 11 => 206
    | 12 => 193
    | 13 => 137
    | 14 => 156
    | 15 => 130
    | 16 => 115
    | 17 => 166
    | 18 => 92
    | 19 => 78
    | 20 => 49
    | 21 => 26
    | 22 => 71
    | 23 => 97
    | 24 => 41
    | 25 => 167
    | _ => 112
  point := fun i =>
    match i.val with
    | 0 => 565 / 2
    | 1 => 166470577112813 / 800000000000
    | 2 => 53833164284429 / 160000000000
    | 3 => 48575699217991 / 800000000000
    | 4 => 130481160836827 / 800000000000
    | 5 => 354281733872559 / 800000000000
    | 6 => 260962321673767 / 800000000000
    | 7 => 447163386148291 / 800000000000
    | 8 => 329378526352969 / 800000000000
    | 9 => 505351362914887 / 800000000000
    | 10 => 291764745414223 / 800000000000
    | 11 => 517741660719707 / 800000000000
    | 12 => 483741419126183 / 800000000000
    | 13 => 345220702353239 / 800000000000
    | 14 => 391443482510481 / 800000000000
    | 15 => 326344765682689 / 800000000000
    | 16 => 288335497524469 / 800000000000
    | 17 => 83570865598431 / 160000000000
    | 18 => 231161412338957 / 800000000000
    | 19 => 195958089282277 / 800000000000
    | 20 => 122621473647031 / 800000000000
    | 21 => 65946236347977 / 800000000000
    | 22 => 179056860054931 / 800000000000
    | 23 => 244486834363187 / 800000000000
    | 24 => 103378526352969 / 800000000000
    | 25 => 420227970220649 / 800000000000
    | _ => 280692809035591 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))
    | 1 => (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))
    | 2 => (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000))
    | 3 => (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))
    | 4 => (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))
    | 5 => (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000))
    | 6 => (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))
    | 7 => (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))
    | 8 => (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000))
    | 9 => (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))
    | 10 => (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))
    | 11 => (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000))
    | 12 => (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))
    | 13 => (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))
    | 14 => (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000))
    | 15 => (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))
    | 16 => (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))
    | 17 => (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000))
    | 18 => (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))
    | 19 => (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))
    | 20 => (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000))
    | 21 => (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))
    | 22 => (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))
    | 23 => (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000))
    | 24 => (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))
    | 25 => (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))
    | _ => (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (7949570795 / 1000000000000) (7949570816 / 1000000000000)
      | 1 => orderedInterval (3897945798 / 1000000000000) (3897945839 / 1000000000000)
      | 2 => orderedInterval (-1309828692 / 1000000000000) (-1309828676 / 1000000000000)
      | 3 => orderedInterval (10679758546 / 1000000000000) (10679758658 / 1000000000000)
      | 4 => orderedInterval (-3867927566 / 1000000000000) (-3867925819 / 1000000000000)
      | 5 => orderedInterval (843100078 / 1000000000000) (843100128 / 1000000000000)
      | 6 => orderedInterval (-6984325210 / 1000000000000) (-6984325138 / 1000000000000)
      | 7 => orderedInterval (3072346447 / 1000000000000) (3072346519 / 1000000000000)
      | _ => orderedInterval (4053833193 / 1000000000000) (4053833283 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14724263406 / 1000000000000) (14724263430 / 1000000000000)
      | 1 => orderedInterval (4381405923 / 1000000000000) (4381405964 / 1000000000000)
      | 2 => orderedInterval (-2563311038 / 1000000000000) (-2563311010 / 1000000000000)
      | 3 => orderedInterval (15734403874 / 1000000000000) (15734404107 / 1000000000000)
      | 4 => orderedInterval (2364226454 / 1000000000000) (2364229290 / 1000000000000)
      | 5 => orderedInterval (3638932285 / 1000000000000) (3638932365 / 1000000000000)
      | 6 => orderedInterval (-8870221780 / 1000000000000) (-8870221714 / 1000000000000)
      | 7 => orderedInterval (-338541861 / 1000000000000) (-338541790 / 1000000000000)
      | _ => orderedInterval (-9020653133 / 1000000000000) (-9020653004 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6818137869 / 1000000000000) (-6818137842 / 1000000000000)
      | 1 => orderedInterval (-4572594291 / 1000000000000) (-4572594236 / 1000000000000)
      | 2 => orderedInterval (3743113935 / 1000000000000) (3743113985 / 1000000000000)
      | 3 => orderedInterval (-45211084408 / 1000000000000) (-45211083908 / 1000000000000)
      | 4 => orderedInterval (10019582063 / 1000000000000) (10019586765 / 1000000000000)
      | 5 => orderedInterval (-3048773301 / 1000000000000) (-3048773167 / 1000000000000)
      | 6 => orderedInterval (6604684855 / 1000000000000) (6604684919 / 1000000000000)
      | 7 => orderedInterval (-4697723025 / 1000000000000) (-4697722952 / 1000000000000)
      | _ => orderedInterval (-12115849693 / 1000000000000) (-12115849498 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14108345755 / 1000000000000) (-14108345724 / 1000000000000)
      | 1 => orderedInterval (-8474451358 / 1000000000000) (-8474451277 / 1000000000000)
      | 2 => orderedInterval (8600893266 / 1000000000000) (8600893356 / 1000000000000)
      | 3 => orderedInterval (-73863345018 / 1000000000000) (-73863343924 / 1000000000000)
      | 4 => orderedInterval (-7170478420 / 1000000000000) (-7170470468 / 1000000000000)
      | 5 => orderedInterval (-6113888363 / 1000000000000) (-6113888134 / 1000000000000)
      | 6 => orderedInterval (7839626561 / 1000000000000) (7839626622 / 1000000000000)
      | 7 => orderedInterval (405859769 / 1000000000000) (405859847 / 1000000000000)
      | _ => orderedInterval (12400904074 / 1000000000000) (12400904379 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5393275967 / 1000000000000) (5393276003 / 1000000000000)
      | 1 => orderedInterval (10331425114 / 1000000000000) (10331425238 / 1000000000000)
      | 2 => orderedInterval (-11718616167 / 1000000000000) (-11718616001 / 1000000000000)
      | 3 => orderedInterval (215387197123 / 1000000000000) (215387199552 / 1000000000000)
      | 4 => orderedInterval (-27941782650 / 1000000000000) (-27941768826 / 1000000000000)
      | 5 => orderedInterval (10587064684 / 1000000000000) (10587065084 / 1000000000000)
      | 6 => orderedInterval (-6469571092 / 1000000000000) (-6469571031 / 1000000000000)
      | 7 => orderedInterval (5233993145 / 1000000000000) (5233993228 / 1000000000000)
      | _ => orderedInterval (37321034297 / 1000000000000) (37321034796 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (18334473389 / 1000000000000) (18334475610 / 1000000000000)
    | 1 => orderedInterval (20050504130 / 1000000000000) (20050507638 / 1000000000000)
    | 2 => orderedInterval (-56096781734 / 1000000000000) (-56096775934 / 1000000000000)
    | 3 => orderedInterval (-80483225244 / 1000000000000) (-80483215323 / 1000000000000)
    | _ => orderedInterval (238124020421 / 1000000000000) (238124038043 / 1000000000000)

theorem compactCertificate411_stateChecks0 :
    compactCertificate411.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (565 / 2)) (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166470577112813 / 800000000000)) (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (53833164284429 / 160000000000)) (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks1 :
    compactCertificate411.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (48575699217991 / 800000000000)) (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (130481160836827 / 800000000000)) (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (354281733872559 / 800000000000)) (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks2 :
    compactCertificate411.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (260962321673767 / 800000000000)) (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (447163386148291 / 800000000000)) (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (329378526352969 / 800000000000)) (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks3 :
    compactCertificate411.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (505351362914887 / 800000000000)) (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (291764745414223 / 800000000000)) (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (517741660719707 / 800000000000)) (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks4 :
    compactCertificate411.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (483741419126183 / 800000000000)) (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (345220702353239 / 800000000000)) (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (391443482510481 / 800000000000)) (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks5 :
    compactCertificate411.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (326344765682689 / 800000000000)) (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (288335497524469 / 800000000000)) (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (83570865598431 / 160000000000)) (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks6 :
    compactCertificate411.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (231161412338957 / 800000000000)) (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (195958089282277 / 800000000000)) (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (122621473647031 / 800000000000)) (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks7 :
    compactCertificate411.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (65946236347977 / 800000000000)) (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (179056860054931 / 800000000000)) (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (244486834363187 / 800000000000)) (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_stateChecks8 :
    compactCertificate411.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (103378526352969 / 800000000000)) (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (420227970220649 / 800000000000)) (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280692809035591 / 800000000000)) (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_states : ∀ j,
    BesselStateValid (compactCertificate411.point j) (compactCertificate411.state j) :=
  compactCertificate411.statesValid_of_checks3 compactCertificate411_stateChecks0
    compactCertificate411_stateChecks1 compactCertificate411_stateChecks2
    compactCertificate411_stateChecks3 compactCertificate411_stateChecks4
    compactCertificate411_stateChecks5 compactCertificate411_stateChecks6
    compactCertificate411_stateChecks7 compactCertificate411_stateChecks8

theorem compactCertificate411_chunkChecks0_0 :
    compactCertificate411.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (565 / 2) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (166470577112813 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (53833164284429 / 160000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000)))) (orderedInterval (7949570795 / 1000000000000) (7949570816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (48575699217991 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (130481160836827 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (354281733872559 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000)))) (orderedInterval (3897945798 / 1000000000000) (3897945839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (260962321673767 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (447163386148291 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (329378526352969 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000)))) (orderedInterval (-1309828692 / 1000000000000) (-1309828676 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks0_1 :
    compactCertificate411.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (505351362914887 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (291764745414223 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (517741660719707 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000)))) (orderedInterval (10679758546 / 1000000000000) (10679758658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (483741419126183 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (345220702353239 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (391443482510481 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000)))) (orderedInterval (-3867927566 / 1000000000000) (-3867925819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (326344765682689 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (288335497524469 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (83570865598431 / 160000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000)))) (orderedInterval (843100078 / 1000000000000) (843100128 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks0_2 :
    compactCertificate411.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (231161412338957 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (195958089282277 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (122621473647031 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000)))) (orderedInterval (-6984325210 / 1000000000000) (-6984325138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (65946236347977 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (179056860054931 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (244486834363187 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000)))) (orderedInterval (3072346447 / 1000000000000) (3072346519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (103378526352969 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (420227970220649 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (280692809035591 / 800000000000) 0 (IntervalRat.scale (565 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000)))) (orderedInterval (4053833193 / 1000000000000) (4053833283 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks0 :
    compactCertificate411.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate411.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate411_chunkChecks0_0
    compactCertificate411_chunkChecks0_1 compactCertificate411_chunkChecks0_2

theorem compactCertificate411_chunkChecks1_0 :
    compactCertificate411.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (565 / 2) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (166470577112813 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (53833164284429 / 160000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000)))) (orderedInterval (14724263406 / 1000000000000) (14724263430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (48575699217991 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (130481160836827 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (354281733872559 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000)))) (orderedInterval (4381405923 / 1000000000000) (4381405964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (260962321673767 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (447163386148291 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (329378526352969 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000)))) (orderedInterval (-2563311038 / 1000000000000) (-2563311010 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks1_1 :
    compactCertificate411.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (505351362914887 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (291764745414223 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (517741660719707 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000)))) (orderedInterval (15734403874 / 1000000000000) (15734404107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (483741419126183 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (345220702353239 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (391443482510481 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000)))) (orderedInterval (2364226454 / 1000000000000) (2364229290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (326344765682689 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (288335497524469 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (83570865598431 / 160000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000)))) (orderedInterval (3638932285 / 1000000000000) (3638932365 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks1_2 :
    compactCertificate411.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (231161412338957 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (195958089282277 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (122621473647031 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000)))) (orderedInterval (-8870221780 / 1000000000000) (-8870221714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (65946236347977 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (179056860054931 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (244486834363187 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000)))) (orderedInterval (-338541861 / 1000000000000) (-338541790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (103378526352969 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (420227970220649 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (280692809035591 / 800000000000) 1 (IntervalRat.scale (565 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000)))) (orderedInterval (-9020653133 / 1000000000000) (-9020653004 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks1 :
    compactCertificate411.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate411.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate411_chunkChecks1_0
    compactCertificate411_chunkChecks1_1 compactCertificate411_chunkChecks1_2

theorem compactCertificate411_chunkChecks2_0 :
    compactCertificate411.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (565 / 2) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (166470577112813 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (53833164284429 / 160000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000)))) (orderedInterval (-6818137869 / 1000000000000) (-6818137842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (48575699217991 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (130481160836827 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (354281733872559 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000)))) (orderedInterval (-4572594291 / 1000000000000) (-4572594236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (260962321673767 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (447163386148291 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (329378526352969 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000)))) (orderedInterval (3743113935 / 1000000000000) (3743113985 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks2_1 :
    compactCertificate411.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (505351362914887 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (291764745414223 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (517741660719707 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000)))) (orderedInterval (-45211084408 / 1000000000000) (-45211083908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (483741419126183 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (345220702353239 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (391443482510481 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000)))) (orderedInterval (10019582063 / 1000000000000) (10019586765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (326344765682689 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (288335497524469 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (83570865598431 / 160000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000)))) (orderedInterval (-3048773301 / 1000000000000) (-3048773167 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks2_2 :
    compactCertificate411.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (231161412338957 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (195958089282277 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (122621473647031 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000)))) (orderedInterval (6604684855 / 1000000000000) (6604684919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (65946236347977 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (179056860054931 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (244486834363187 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000)))) (orderedInterval (-4697723025 / 1000000000000) (-4697722952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (103378526352969 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (420227970220649 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (280692809035591 / 800000000000) 2 (IntervalRat.scale (565 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000)))) (orderedInterval (-12115849693 / 1000000000000) (-12115849498 / 1000000000000))) = true
  rfl'

theorem compactCertificate411_chunkChecks2 :
    compactCertificate411.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate411.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate411_chunkChecks2_0
    compactCertificate411_chunkChecks2_1 compactCertificate411_chunkChecks2_2

theorem compactCertificate411_chunkChecks3_0 :
    compactCertificate411.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (565 / 2) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (166470577112813 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (53833164284429 / 160000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000)))) (orderedInterval (-14108345755 / 1000000000000) (-14108345724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (48575699217991 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (130481160836827 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (354281733872559 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000)))) (orderedInterval (-8474451358 / 1000000000000) (-8474451277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (260962321673767 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (447163386148291 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (329378526352969 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000)))) (orderedInterval (8600893266 / 1000000000000) (8600893356 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate411_chunkChecks3_1 :
    compactCertificate411.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (505351362914887 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (291764745414223 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (517741660719707 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000)))) (orderedInterval (-73863345018 / 1000000000000) (-73863343924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (483741419126183 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (345220702353239 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (391443482510481 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000)))) (orderedInterval (-7170478420 / 1000000000000) (-7170470468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (326344765682689 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (288335497524469 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (83570865598431 / 160000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000)))) (orderedInterval (-6113888363 / 1000000000000) (-6113888134 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate411_chunkChecks3_2 :
    compactCertificate411.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (231161412338957 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (195958089282277 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (122621473647031 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000)))) (orderedInterval (7839626561 / 1000000000000) (7839626622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (65946236347977 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (179056860054931 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (244486834363187 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000)))) (orderedInterval (405859769 / 1000000000000) (405859847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (103378526352969 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (420227970220649 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (280692809035591 / 800000000000) 3 (IntervalRat.scale (565 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000)))) (orderedInterval (12400904074 / 1000000000000) (12400904379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate411_chunkChecks3 :
    compactCertificate411.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate411.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate411_chunkChecks3_0
    compactCertificate411_chunkChecks3_1 compactCertificate411_chunkChecks3_2

theorem compactCertificate411_chunkChecks4_0 :
    compactCertificate411.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (565 / 2) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24472469656 / 1000000000000) (24472469657 / 1000000000000), orderedInterval (40633721327 / 1000000000000) (40633721328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (166470577112813 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55260659115 / 1000000000000) (55260659153 / 1000000000000), orderedInterval (2238954287 / 1000000000000) (2238954326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (53833164284429 / 160000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38604935017 / 1000000000000) (-38604935016 / 1000000000000), orderedInterval (-19987191187 / 1000000000000) (-19987191186 / 1000000000000)))) (orderedInterval (5393275967 / 1000000000000) (5393276003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (48575699217991 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-99411130826 / 1000000000000) (-99411130143 / 1000000000000), orderedInterval (25347980952 / 1000000000000) (25347981635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (130481160836827 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31219708655 / 1000000000000) (31219708656 / 1000000000000), orderedInterval (54020395520 / 1000000000000) (54020395521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (354281733872559 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23625375498 / 1000000000000) (-23625375497 / 1000000000000), orderedInterval (-29627777638 / 1000000000000) (-29627777637 / 1000000000000)))) (orderedInterval (10331425114 / 1000000000000) (10331425238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (260962321673767 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11454394011 / 1000000000000) (11454394012 / 1000000000000), orderedInterval (42648653768 / 1000000000000) (42648653769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (447163386148291 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17232820418 / 1000000000000) (17232820419 / 1000000000000), orderedInterval (29001442970 / 1000000000000) (29001442971 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (329378526352969 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32203686040 / 1000000000000) (-32203686039 / 1000000000000), orderedInterval (-22525350957 / 1000000000000) (-22525350956 / 1000000000000)))) (orderedInterval (-11718616167 / 1000000000000) (-11718616001 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate411_chunkChecks4_1 :
    compactCertificate411.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (505351362914887 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26955505741 / 1000000000000) (-26955505740 / 1000000000000), orderedInterval (-16747860186 / 1000000000000) (-16747860185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (291764745414223 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36573742178 / 1000000000000) (36573742179 / 1000000000000), orderedInterval (20147150984 / 1000000000000) (20147150985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (517741660719707 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22371759044 / 1000000000000) (22371759045 / 1000000000000), orderedInterval (21964334144 / 1000000000000) (21964334145 / 1000000000000)))) (orderedInterval (215387197123 / 1000000000000) (215387199552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (483741419126183 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24704236082 / 1000000000000) (24704250966 / 1000000000000), orderedInterval (-21056757167 / 1000000000000) (-21056742283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (345220702353239 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-36184916398 / 1000000000000) (-36184901127 / 1000000000000), orderedInterval (12923207450 / 1000000000000) (12923222721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (391443482510481 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37580877 / 1000000000000) (37580878 / 1000000000000), orderedInterval (36070315166 / 1000000000000) (36070315167 / 1000000000000)))) (orderedInterval (-27941782650 / 1000000000000) (-27941768826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (326344765682689 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12013707225 / 1000000000000) (12013707226 / 1000000000000), orderedInterval (37618750156 / 1000000000000) (37618750157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (288335497524469 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3305504936 / 1000000000000) (3305504939 / 1000000000000), orderedInterval (-41902150416 / 1000000000000) (-41902150413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (83570865598431 / 160000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34898241436 / 1000000000000) (34898242289 / 1000000000000), orderedInterval (-1007042653 / 1000000000000) (-1007041800 / 1000000000000)))) (orderedInterval (10587064684 / 1000000000000) (10587065084 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate411_chunkChecks4_2 :
    compactCertificate411.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (231161412338957 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30603311056 / 1000000000000) (30603311057 / 1000000000000), orderedInterval (35536960789 / 1000000000000) (35536960790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (195958089282277 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32382930841 / 1000000000000) (32382930842 / 1000000000000), orderedInterval (39308390666 / 1000000000000) (39308390667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (122621473647031 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7931575042 / 1000000000000) (-7931575040 / 1000000000000), orderedInterval (-63931220547 / 1000000000000) (-63931220545 / 1000000000000)))) (orderedInterval (-6469571092 / 1000000000000) (-6469571031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (65946236347977 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87823735359 / 1000000000000) (87823735376 / 1000000000000), orderedInterval (2588892464 / 1000000000000) (2588892481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (179056860054931 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53323541348 / 1000000000000) (-53323541285 / 1000000000000), orderedInterval (-838674591 / 1000000000000) (-838674528 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (244486834363187 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45463590819 / 1000000000000) (-45463590354 / 1000000000000), orderedInterval (4096922617 / 1000000000000) (4096923081 / 1000000000000)))) (orderedInterval (5233993145 / 1000000000000) (5233993228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (103378526352969 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65476843393 / 1000000000000) (-65476843392 / 1000000000000), orderedInterval (-25030450263 / 1000000000000) (-25030450262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (420227970220649 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34439421772 / 1000000000000) (-34439421683 / 1000000000000), orderedInterval (-5054159065 / 1000000000000) (-5054158977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (280692809035591 / 800000000000) 4 (IntervalRat.scale (565 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8768051230 / 1000000000000) (-8768051207 / 1000000000000), orderedInterval (41696390249 / 1000000000000) (41696390272 / 1000000000000)))) (orderedInterval (37321034297 / 1000000000000) (37321034796 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate411_chunkChecks4 :
    compactCertificate411.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate411.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate411_chunkChecks4_0
    compactCertificate411_chunkChecks4_1 compactCertificate411_chunkChecks4_2

theorem compactCertificate411_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate411.chunkCheck r b = true :=
  compactCertificate411.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate411_chunkChecks0
    · exact compactCertificate411_chunkChecks1
    · exact compactCertificate411_chunkChecks2
    · exact compactCertificate411_chunkChecks3
    · exact compactCertificate411_chunkChecks4)

theorem compactCertificate411_coefficient0 :
    compactCertificate411.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate411_coefficient1 :
    compactCertificate411.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate411_coefficient2 :
    compactCertificate411.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate411_coefficient3 :
    compactCertificate411.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate411_coefficient4 :
    compactCertificate411.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate411_coefficients : ∀ r : Fin 5,
    compactCertificate411.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate411_coefficient0
  · exact compactCertificate411_coefficient1
  · exact compactCertificate411_coefficient2
  · exact compactCertificate411_coefficient3
  · exact compactCertificate411_coefficient4

theorem compactCertificate411_lower : (1 : ℚ) ≤ compactCertificate411.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate411, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate411_proves {t : ℝ} (ht : t ∈ compactCertificate411.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate411.proves compactCertificate411_states compactCertificate411_chunks
    compactCertificate411_coefficients compactCertificate411_lower ht

end Erdos232
