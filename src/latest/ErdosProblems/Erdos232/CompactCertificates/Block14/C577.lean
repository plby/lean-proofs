/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate577 : CompactCertificate where
  left := 448
  right := 449
  center := 897 / 2
  grid := fun i =>
    match i.val with
    | 0 => 143
    | 1 => 105
    | 2 => 170
    | 3 => 31
    | 4 => 82
    | 5 => 224
    | 6 => 165
    | 7 => 283
    | 8 => 208
    | 9 => 319
    | 10 => 184
    | 11 => 327
    | 12 => 306
    | 13 => 218
    | 14 => 247
    | 15 => 206
    | 16 => 182
    | 17 => 264
    | 18 => 146
    | 19 => 124
    | 20 => 77
    | 21 => 42
    | 22 => 113
    | 23 => 155
    | 24 => 65
    | 25 => 266
    | _ => 177
  point := fun i =>
    match i.val with
    | 0 => 897 / 2
    | 1 => 1321452280267197 / 4000000000000
    | 2 => 427330516487901 / 800000000000
    | 3 => 385596479633079 / 4000000000000
    | 4 => 1035766382925963 / 4000000000000
    | 5 => 2812307214899871 / 4000000000000
    | 6 => 2071532765852823 / 4000000000000
    | 7 => 3549606702433779 / 4000000000000
    | 8 => 2614624231315161 / 4000000000000
    | 9 => 4011505951634103 / 4000000000000
    | 10 => 2316044041031487 / 4000000000000
    | 11 => 4109860793500683 / 4000000000000
    | 12 => 3839965070408727 / 4000000000000
    | 13 => 2740380265582791 / 4000000000000
    | 14 => 3107299148777889 / 4000000000000
    | 15 => 2590542078029841 / 4000000000000
    | 16 => 2288822489198661 / 4000000000000
    | 17 => 663389968511439 / 800000000000
    | 18 => 1834971565203933 / 4000000000000
    | 19 => 1555525717577013 / 4000000000000
    | 20 => 973375768684839 / 4000000000000
    | 21 => 523484725700313 / 4000000000000
    | 22 => 1421362862559939 / 4000000000000
    | 23 => 1940749472776803 / 4000000000000
    | 24 => 820624231315161 / 4000000000000
    | 25 => 3335791940601081 / 4000000000000
    | _ => 2228154422167479 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))
    | 1 => (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))
    | 2 => (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000))
    | 3 => (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))
    | 4 => (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
    | 5 => (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000))
    | 6 => (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))
    | 7 => (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))
    | 8 => (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000))
    | 9 => (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))
    | 10 => (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))
    | 11 => (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000))
    | 12 => (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))
    | 13 => (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))
    | 14 => (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000))
    | 15 => (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))
    | 16 => (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))
    | 17 => (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000))
    | 18 => (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))
    | 19 => (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))
    | 20 => (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000))
    | 21 => (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))
    | 22 => (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))
    | 23 => (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000))
    | 24 => (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))
    | 25 => (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))
    | _ => (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (608328653 / 1000000000000) (608328685 / 1000000000000)
      | 1 => orderedInterval (1057865050 / 1000000000000) (1057866735 / 1000000000000)
      | 2 => orderedInterval (-8166306 / 1000000000000) (-8166151 / 1000000000000)
      | 3 => orderedInterval (4006333684 / 1000000000000) (4006335029 / 1000000000000)
      | 4 => orderedInterval (2833674032 / 1000000000000) (2833674114 / 1000000000000)
      | 5 => orderedInterval (-1024351946 / 1000000000000) (-1024351902 / 1000000000000)
      | 6 => orderedInterval (-6065729544 / 1000000000000) (-6065725930 / 1000000000000)
      | 7 => orderedInterval (-1060197805 / 1000000000000) (-1060192402 / 1000000000000)
      | _ => orderedInterval (7699800267 / 1000000000000) (7699802325 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13467813402 / 1000000000000) (-13467813366 / 1000000000000)
      | 1 => orderedInterval (-3675737277 / 1000000000000) (-3675736275 / 1000000000000)
      | 2 => orderedInterval (1639859006 / 1000000000000) (1639859306 / 1000000000000)
      | 3 => orderedInterval (-4494897734 / 1000000000000) (-4494895169 / 1000000000000)
      | 4 => orderedInterval (1462825366 / 1000000000000) (1462825503 / 1000000000000)
      | 5 => orderedInterval (380272160 / 1000000000000) (380272224 / 1000000000000)
      | 6 => orderedInterval (-5412176937 / 1000000000000) (-5412174932 / 1000000000000)
      | 7 => orderedInterval (1655607098 / 1000000000000) (1655612928 / 1000000000000)
      | _ => orderedInterval (-3978070173 / 1000000000000) (-3978067149 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1409682901 / 1000000000000) (-1409682860 / 1000000000000)
      | 1 => orderedInterval (261510194 / 1000000000000) (261510824 / 1000000000000)
      | 2 => orderedInterval (1157489315 / 1000000000000) (1157489899 / 1000000000000)
      | 3 => orderedInterval (-11239516449 / 1000000000000) (-11239511277 / 1000000000000)
      | 4 => orderedInterval (-7258567245 / 1000000000000) (-7258567014 / 1000000000000)
      | 5 => orderedInterval (748235390 / 1000000000000) (748235483 / 1000000000000)
      | 6 => orderedInterval (5292175216 / 1000000000000) (5292176351 / 1000000000000)
      | 7 => orderedInterval (2108634194 / 1000000000000) (2108640508 / 1000000000000)
      | _ => orderedInterval (-15763553060 / 1000000000000) (-15763548419 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12787192668 / 1000000000000) (12787192716 / 1000000000000)
      | 1 => orderedInterval (8325139413 / 1000000000000) (8325139855 / 1000000000000)
      | 2 => orderedInterval (-5343544729 / 1000000000000) (-5343543586 / 1000000000000)
      | 3 => orderedInterval (21847431321 / 1000000000000) (21847442161 / 1000000000000)
      | 4 => orderedInterval (-1479073939 / 1000000000000) (-1479073543 / 1000000000000)
      | 5 => orderedInterval (-2575299854 / 1000000000000) (-2575299710 / 1000000000000)
      | 6 => orderedInterval (5484466658 / 1000000000000) (5484467317 / 1000000000000)
      | 7 => orderedInterval (-2156141590 / 1000000000000) (-2156134762 / 1000000000000)
      | _ => orderedInterval (10994602194 / 1000000000000) (10994609597 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2404933225 / 1000000000000) (2404933281 / 1000000000000)
      | 1 => orderedInterval (-1735555923 / 1000000000000) (-1735555545 / 1000000000000)
      | 2 => orderedInterval (-6920360315 / 1000000000000) (-6920358070 / 1000000000000)
      | 3 => orderedInterval (38955409887 / 1000000000000) (38955433228 / 1000000000000)
      | 4 => orderedInterval (19730940763 / 1000000000000) (19730941454 / 1000000000000)
      | 5 => orderedInterval (1721555844 / 1000000000000) (1721556072 / 1000000000000)
      | 6 => orderedInterval (-5201148152 / 1000000000000) (-5201147750 / 1000000000000)
      | 7 => orderedInterval (-2791788306 / 1000000000000) (-2791780907 / 1000000000000)
      | _ => orderedInterval (36313135142 / 1000000000000) (36313147401 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (8047556085 / 1000000000000) (8047570503 / 1000000000000)
    | 1 => orderedInterval (-25890131893 / 1000000000000) (-25890116930 / 1000000000000)
    | 2 => orderedInterval (-26103275346 / 1000000000000) (-26103256505 / 1000000000000)
    | 3 => orderedInterval (47884772142 / 1000000000000) (47884800045 / 1000000000000)
    | _ => orderedInterval (82477122165 / 1000000000000) (82477169164 / 1000000000000)

theorem compactCertificate577_stateChecks0 :
    compactCertificate577.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (897 / 2)) (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1321452280267197 / 4000000000000)) (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (427330516487901 / 800000000000)) (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks1 :
    compactCertificate577.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (385596479633079 / 4000000000000)) (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035766382925963 / 4000000000000)) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2812307214899871 / 4000000000000)) (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks2 :
    compactCertificate577.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2071532765852823 / 4000000000000)) (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (3549606702433779 / 4000000000000)) (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2614624231315161 / 4000000000000)) (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks3 :
    compactCertificate577.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 319 12 (4011505951634103 / 4000000000000)) (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2316044041031487 / 4000000000000)) (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 327 12 (4109860793500683 / 4000000000000)) (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks4 :
    compactCertificate577.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 306 12 (3839965070408727 / 4000000000000)) (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2740380265582791 / 4000000000000)) (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3107299148777889 / 4000000000000)) (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks5 :
    compactCertificate577.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2590542078029841 / 4000000000000)) (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2288822489198661 / 4000000000000)) (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (663389968511439 / 800000000000)) (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks6 :
    compactCertificate577.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1834971565203933 / 4000000000000)) (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1555525717577013 / 4000000000000)) (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (973375768684839 / 4000000000000)) (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks7 :
    compactCertificate577.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (523484725700313 / 4000000000000)) (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1421362862559939 / 4000000000000)) (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1940749472776803 / 4000000000000)) (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_stateChecks8 :
    compactCertificate577.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820624231315161 / 4000000000000)) (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3335791940601081 / 4000000000000)) (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2228154422167479 / 4000000000000)) (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_states : ∀ j,
    BesselStateValid (compactCertificate577.point j) (compactCertificate577.state j) :=
  compactCertificate577.statesValid_of_checks3 compactCertificate577_stateChecks0
    compactCertificate577_stateChecks1 compactCertificate577_stateChecks2
    compactCertificate577_stateChecks3 compactCertificate577_stateChecks4
    compactCertificate577_stateChecks5 compactCertificate577_stateChecks6
    compactCertificate577_stateChecks7 compactCertificate577_stateChecks8

theorem compactCertificate577_chunkChecks0_0 :
    compactCertificate577.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (897 / 2) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1321452280267197 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (427330516487901 / 800000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000)))) (orderedInterval (608328653 / 1000000000000) (608328685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (385596479633079 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2812307214899871 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000)))) (orderedInterval (1057865050 / 1000000000000) (1057866735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2071532765852823 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3549606702433779 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2614624231315161 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000)))) (orderedInterval (-8166306 / 1000000000000) (-8166151 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks0_1 :
    compactCertificate577.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4011505951634103 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2316044041031487 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4109860793500683 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000)))) (orderedInterval (4006333684 / 1000000000000) (4006335029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3839965070408727 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2740380265582791 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3107299148777889 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000)))) (orderedInterval (2833674032 / 1000000000000) (2833674114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2590542078029841 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2288822489198661 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (663389968511439 / 800000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000)))) (orderedInterval (-1024351946 / 1000000000000) (-1024351902 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks0_2 :
    compactCertificate577.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1834971565203933 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1555525717577013 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (973375768684839 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000)))) (orderedInterval (-6065729544 / 1000000000000) (-6065725930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (523484725700313 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1421362862559939 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1940749472776803 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000)))) (orderedInterval (-1060197805 / 1000000000000) (-1060192402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (820624231315161 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3335791940601081 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2228154422167479 / 4000000000000) 0 (IntervalRat.scale (897 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000)))) (orderedInterval (7699800267 / 1000000000000) (7699802325 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks0 :
    compactCertificate577.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate577.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate577_chunkChecks0_0
    compactCertificate577_chunkChecks0_1 compactCertificate577_chunkChecks0_2

theorem compactCertificate577_chunkChecks1_0 :
    compactCertificate577.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (897 / 2) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1321452280267197 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (427330516487901 / 800000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000)))) (orderedInterval (-13467813402 / 1000000000000) (-13467813366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (385596479633079 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2812307214899871 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000)))) (orderedInterval (-3675737277 / 1000000000000) (-3675736275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2071532765852823 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3549606702433779 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2614624231315161 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000)))) (orderedInterval (1639859006 / 1000000000000) (1639859306 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks1_1 :
    compactCertificate577.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4011505951634103 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2316044041031487 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4109860793500683 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000)))) (orderedInterval (-4494897734 / 1000000000000) (-4494895169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3839965070408727 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2740380265582791 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3107299148777889 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000)))) (orderedInterval (1462825366 / 1000000000000) (1462825503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2590542078029841 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2288822489198661 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (663389968511439 / 800000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000)))) (orderedInterval (380272160 / 1000000000000) (380272224 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks1_2 :
    compactCertificate577.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1834971565203933 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1555525717577013 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (973375768684839 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000)))) (orderedInterval (-5412176937 / 1000000000000) (-5412174932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (523484725700313 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1421362862559939 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1940749472776803 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000)))) (orderedInterval (1655607098 / 1000000000000) (1655612928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (820624231315161 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3335791940601081 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2228154422167479 / 4000000000000) 1 (IntervalRat.scale (897 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000)))) (orderedInterval (-3978070173 / 1000000000000) (-3978067149 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks1 :
    compactCertificate577.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate577.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate577_chunkChecks1_0
    compactCertificate577_chunkChecks1_1 compactCertificate577_chunkChecks1_2

theorem compactCertificate577_chunkChecks2_0 :
    compactCertificate577.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (897 / 2) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1321452280267197 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (427330516487901 / 800000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000)))) (orderedInterval (-1409682901 / 1000000000000) (-1409682860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (385596479633079 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2812307214899871 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000)))) (orderedInterval (261510194 / 1000000000000) (261510824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2071532765852823 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3549606702433779 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2614624231315161 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000)))) (orderedInterval (1157489315 / 1000000000000) (1157489899 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks2_1 :
    compactCertificate577.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4011505951634103 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2316044041031487 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4109860793500683 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000)))) (orderedInterval (-11239516449 / 1000000000000) (-11239511277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3839965070408727 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2740380265582791 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3107299148777889 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000)))) (orderedInterval (-7258567245 / 1000000000000) (-7258567014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2590542078029841 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2288822489198661 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (663389968511439 / 800000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000)))) (orderedInterval (748235390 / 1000000000000) (748235483 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks2_2 :
    compactCertificate577.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1834971565203933 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1555525717577013 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (973375768684839 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000)))) (orderedInterval (5292175216 / 1000000000000) (5292176351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (523484725700313 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1421362862559939 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1940749472776803 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000)))) (orderedInterval (2108634194 / 1000000000000) (2108640508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (820624231315161 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3335791940601081 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2228154422167479 / 4000000000000) 2 (IntervalRat.scale (897 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000)))) (orderedInterval (-15763553060 / 1000000000000) (-15763548419 / 1000000000000))) = true
  rfl'

theorem compactCertificate577_chunkChecks2 :
    compactCertificate577.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate577.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate577_chunkChecks2_0
    compactCertificate577_chunkChecks2_1 compactCertificate577_chunkChecks2_2

theorem compactCertificate577_chunkChecks3_0 :
    compactCertificate577.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (897 / 2) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1321452280267197 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (427330516487901 / 800000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000)))) (orderedInterval (12787192668 / 1000000000000) (12787192716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (385596479633079 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2812307214899871 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000)))) (orderedInterval (8325139413 / 1000000000000) (8325139855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2071532765852823 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3549606702433779 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2614624231315161 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000)))) (orderedInterval (-5343544729 / 1000000000000) (-5343543586 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate577_chunkChecks3_1 :
    compactCertificate577.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4011505951634103 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2316044041031487 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4109860793500683 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000)))) (orderedInterval (21847431321 / 1000000000000) (21847442161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3839965070408727 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2740380265582791 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3107299148777889 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000)))) (orderedInterval (-1479073939 / 1000000000000) (-1479073543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2590542078029841 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2288822489198661 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (663389968511439 / 800000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000)))) (orderedInterval (-2575299854 / 1000000000000) (-2575299710 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate577_chunkChecks3_2 :
    compactCertificate577.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1834971565203933 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1555525717577013 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (973375768684839 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000)))) (orderedInterval (5484466658 / 1000000000000) (5484467317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (523484725700313 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1421362862559939 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1940749472776803 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000)))) (orderedInterval (-2156141590 / 1000000000000) (-2156134762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (820624231315161 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3335791940601081 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2228154422167479 / 4000000000000) 3 (IntervalRat.scale (897 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000)))) (orderedInterval (10994602194 / 1000000000000) (10994609597 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate577_chunkChecks3 :
    compactCertificate577.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate577.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate577_chunkChecks3_0
    compactCertificate577_chunkChecks3_1 compactCertificate577_chunkChecks3_2

theorem compactCertificate577_chunkChecks4_0 :
    compactCertificate577.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (897 / 2) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1407604488 / 1000000000000) (-1407604487 / 1000000000000), orderedInterval (-37647622100 / 1000000000000) (-37647622099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1321452280267197 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42065739608 / 1000000000000) (-42065739605 / 1000000000000), orderedInterval (-12486329744 / 1000000000000) (-12486329742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (427330516487901 / 800000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26554100644 / 1000000000000) (26554100645 / 1000000000000), orderedInterval (22036136613 / 1000000000000) (22036136614 / 1000000000000)))) (orderedInterval (2404933225 / 1000000000000) (2404933281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (385596479633079 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16634324145 / 1000000000000) (16634324291 / 1000000000000), orderedInterval (-79631109243 / 1000000000000) (-79631109096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1035766382925963 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42397319900 / 1000000000000) (42397364518 / 1000000000000), orderedInterval (-25791982889 / 1000000000000) (-25791938271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2812307214899871 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4355971827 / 1000000000000) (4355971828 / 1000000000000), orderedInterval (29771095444 / 1000000000000) (29771095445 / 1000000000000)))) (orderedInterval (-1735555923 / 1000000000000) (-1735555545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2071532765852823 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10547313329 / 1000000000000) (-10547313328 / 1000000000000), orderedInterval (-33426735880 / 1000000000000) (-33426735879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3549606702433779 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20708177669 / 1000000000000) (20708181855 / 1000000000000), orderedInterval (-16998982828 / 1000000000000) (-16998978643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2614624231315161 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26090540567 / 1000000000000) (26090540568 / 1000000000000), orderedInterval (17103725245 / 1000000000000) (17103725246 / 1000000000000)))) (orderedInterval (-6920360315 / 1000000000000) (-6920358070 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate577_chunkChecks4_1 :
    compactCertificate577.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4011505951634103 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25120283711 / 1000000000000) (-25120279607 / 1000000000000), orderedInterval (-1927881185 / 1000000000000) (-1927877081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2316044041031487 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32667375166 / 1000000000000) (32667381071 / 1000000000000), orderedInterval (-5714786367 / 1000000000000) (-5714780462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4109860793500683 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20242708551 / 1000000000000) (-20242708548 / 1000000000000), orderedInterval (-14475831788 / 1000000000000) (-14475831785 / 1000000000000)))) (orderedInterval (38955409887 / 1000000000000) (38955433228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3839965070408727 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13478019480 / 1000000000000) (-13478019441 / 1000000000000), orderedInterval (21950006434 / 1000000000000) (21950006473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2740380265582791 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25864255741 / 1000000000000) (25864255742 / 1000000000000), orderedInterval (16114416312 / 1000000000000) (16114416313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3107299148777889 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28565146100 / 1000000000000) (-28565140565 / 1000000000000), orderedInterval (1901911745 / 1000000000000) (1901917279 / 1000000000000)))) (orderedInterval (19730940763 / 1000000000000) (19730941454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2590542078029841 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29779187344 / 1000000000000) (29779187361 / 1000000000000), orderedInterval (9784689360 / 1000000000000) (9784689377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2288822489198661 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31334623493 / 1000000000000) (31334623499 / 1000000000000), orderedInterval (11405586205 / 1000000000000) (11405586211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (663389968511439 / 800000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16596822957 / 1000000000000) (16596822958 / 1000000000000), orderedInterval (22176984401 / 1000000000000) (22176984402 / 1000000000000)))) (orderedInterval (1721555844 / 1000000000000) (1721556072 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate577_chunkChecks4_2 :
    compactCertificate577.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1834971565203933 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28121606631 / 1000000000000) (28121606632 / 1000000000000), orderedInterval (24401370383 / 1000000000000) (24401370384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1555525717577013 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4402154034 / 1000000000000) (4402154035 / 1000000000000), orderedInterval (40214683522 / 1000000000000) (40214683523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (973375768684839 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40550588737 / 1000000000000) (-40550481184 / 1000000000000), orderedInterval (31256715483 / 1000000000000) (31256823036 / 1000000000000)))) (orderedInterval (-5201148152 / 1000000000000) (-5201147750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (523484725700313 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20028553382 / 1000000000000) (-20028553021 / 1000000000000), orderedInterval (66884924649 / 1000000000000) (66884925010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1421362862559939 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38204714713 / 1000000000000) (-38204714712 / 1000000000000), orderedInterval (-18166404263 / 1000000000000) (-18166404262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1940749472776803 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29968697355 / 1000000000000) (29968767064 / 1000000000000), orderedInterval (-20377562621 / 1000000000000) (-20377492912 / 1000000000000)))) (orderedInterval (-2791788306 / 1000000000000) (-2791780907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (820624231315161 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54934778647 / 1000000000000) (-54934777993 / 1000000000000), orderedInterval (9367597756 / 1000000000000) (9367598409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3335791940601081 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22155046334 / 1000000000000) (-22155037354 / 1000000000000), orderedInterval (16521905149 / 1000000000000) (16521914129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2228154422167479 / 4000000000000) 4 (IntervalRat.scale (897 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33190972947 / 1000000000000) (-33190966559 / 1000000000000), orderedInterval (6450366775 / 1000000000000) (6450373163 / 1000000000000)))) (orderedInterval (36313135142 / 1000000000000) (36313147401 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate577_chunkChecks4 :
    compactCertificate577.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate577.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate577_chunkChecks4_0
    compactCertificate577_chunkChecks4_1 compactCertificate577_chunkChecks4_2

theorem compactCertificate577_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate577.chunkCheck r b = true :=
  compactCertificate577.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate577_chunkChecks0
    · exact compactCertificate577_chunkChecks1
    · exact compactCertificate577_chunkChecks2
    · exact compactCertificate577_chunkChecks3
    · exact compactCertificate577_chunkChecks4)

theorem compactCertificate577_coefficient0 :
    compactCertificate577.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate577_coefficient1 :
    compactCertificate577.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate577_coefficient2 :
    compactCertificate577.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate577_coefficient3 :
    compactCertificate577.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate577_coefficient4 :
    compactCertificate577.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate577_coefficients : ∀ r : Fin 5,
    compactCertificate577.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate577_coefficient0
  · exact compactCertificate577_coefficient1
  · exact compactCertificate577_coefficient2
  · exact compactCertificate577_coefficient3
  · exact compactCertificate577_coefficient4

theorem compactCertificate577_lower : (1 : ℚ) ≤ compactCertificate577.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate577, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate577_proves {t : ℝ} (ht : t ∈ compactCertificate577.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate577.proves compactCertificate577_states compactCertificate577_chunks
    compactCertificate577_coefficients compactCertificate577_lower ht

end Erdos232
