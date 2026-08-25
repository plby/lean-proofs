/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate573 : CompactCertificate where
  left := 444
  right := 445
  center := 889 / 2
  grid := fun i =>
    match i.val with
    | 0 => 142
    | 1 => 104
    | 2 => 169
    | 3 => 30
    | 4 => 82
    | 5 => 222
    | 6 => 163
    | 7 => 280
    | 8 => 206
    | 9 => 317
    | 10 => 183
    | 11 => 324
    | 12 => 303
    | 13 => 216
    | 14 => 245
    | 15 => 204
    | 16 => 181
    | 17 => 262
    | 18 => 145
    | 19 => 123
    | 20 => 77
    | 21 => 41
    | 22 => 112
    | 23 => 153
    | 24 => 65
    | 25 => 263
    | _ => 176
  point := fun i =>
    match i.val with
    | 0 => 889 / 2
    | 1 => 1309666752683989 / 4000000000000
    | 2 => 423519319016437 / 800000000000
    | 3 => 382157492077823 / 4000000000000
    | 4 => 1026528778618931 / 4000000000000
    | 5 => 2787225322236327 / 4000000000000
    | 6 => 2053057557238751 / 4000000000000
    | 7 => 3517949117573723 / 4000000000000
    | 8 => 2591305397591057 / 4000000000000
    | 9 => 3975728863994111 / 4000000000000
    | 10 => 2295388129851719 / 4000000000000
    | 11 => 4073206516635571 / 4000000000000
    | 12 => 3805717890293599 / 4000000000000
    | 13 => 2715939861876367 / 4000000000000
    | 14 => 3079586335856793 / 4000000000000
    | 15 => 2567438023822217 / 4000000000000
    | 16 => 2268409356630557 / 4000000000000
    | 17 => 657473447053143 / 800000000000
    | 18 => 1818606155480821 / 4000000000000
    | 19 => 1541652578512781 / 4000000000000
    | 20 => 964694602408943 / 4000000000000
    | 21 => 518815965604881 / 4000000000000
    | 22 => 1408686270697643 / 4000000000000
    | 23 => 1923440670344011 / 4000000000000
    | 24 => 813305397591057 / 4000000000000
    | 25 => 3306041287842097 / 4000000000000
    | _ => 2208282364890623 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))
    | 1 => (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))
    | 2 => (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000))
    | 3 => (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))
    | 4 => (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))
    | 5 => (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000))
    | 6 => (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))
    | 7 => (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))
    | 8 => (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000))
    | 9 => (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))
    | 10 => (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))
    | 11 => (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000))
    | 12 => (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))
    | 13 => (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))
    | 14 => (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000))
    | 15 => (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))
    | 16 => (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))
    | 17 => (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000))
    | 18 => (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))
    | 19 => (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))
    | 20 => (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000))
    | 21 => (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))
    | 22 => (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))
    | 23 => (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000))
    | 24 => (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))
    | 25 => (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))
    | _ => (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9189604229 / 1000000000000) (-9189595433 / 1000000000000)
      | 1 => orderedInterval (-1462849614 / 1000000000000) (-1462849404 / 1000000000000)
      | 2 => orderedInterval (264877672 / 1000000000000) (264877704 / 1000000000000)
      | 3 => orderedInterval (-129118419 / 1000000000000) (-129111213 / 1000000000000)
      | 4 => orderedInterval (2949198670 / 1000000000000) (2949198724 / 1000000000000)
      | 5 => orderedInterval (-1259604705 / 1000000000000) (-1259604255 / 1000000000000)
      | 6 => orderedInterval (-1153443723 / 1000000000000) (-1153443610 / 1000000000000)
      | 7 => orderedInterval (2745041944 / 1000000000000) (2745042001 / 1000000000000)
      | _ => orderedInterval (2409221748 / 1000000000000) (2409221872 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (8479264379 / 1000000000000) (8479273253 / 1000000000000)
      | 1 => orderedInterval (-2202457098 / 1000000000000) (-2202457002 / 1000000000000)
      | 2 => orderedInterval (-1190095127 / 1000000000000) (-1190095074 / 1000000000000)
      | 3 => orderedInterval (3752820588 / 1000000000000) (3752836671 / 1000000000000)
      | 4 => orderedInterval (2745477156 / 1000000000000) (2745477244 / 1000000000000)
      | 5 => orderedInterval (2882529874 / 1000000000000) (2882530474 / 1000000000000)
      | 6 => orderedInterval (7135296283 / 1000000000000) (7135296388 / 1000000000000)
      | 7 => orderedInterval (1283011552 / 1000000000000) (1283011602 / 1000000000000)
      | _ => orderedInterval (-5987509980 / 1000000000000) (-5987509807 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8780378843 / 1000000000000) (8780387829 / 1000000000000)
      | 1 => orderedInterval (988063491 / 1000000000000) (988063583 / 1000000000000)
      | 2 => orderedInterval (311454111 / 1000000000000) (311454203 / 1000000000000)
      | 3 => orderedInterval (2078801244 / 1000000000000) (2078837212 / 1000000000000)
      | 4 => orderedInterval (-7291268472 / 1000000000000) (-7291268327 / 1000000000000)
      | 5 => orderedInterval (2458590430 / 1000000000000) (2458591238 / 1000000000000)
      | 6 => orderedInterval (974177973 / 1000000000000) (974178073 / 1000000000000)
      | 7 => orderedInterval (-2286440497 / 1000000000000) (-2286440449 / 1000000000000)
      | _ => orderedInterval (-7428239714 / 1000000000000) (-7428239457 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-7739804432 / 1000000000000) (-7739795335 / 1000000000000)
      | 1 => orderedInterval (7823613270 / 1000000000000) (7823613398 / 1000000000000)
      | 2 => orderedInterval (4907917080 / 1000000000000) (4907917241 / 1000000000000)
      | 3 => orderedInterval (-29690625621 / 1000000000000) (-29690545226 / 1000000000000)
      | 4 => orderedInterval (-8619801563 / 1000000000000) (-8619801319 / 1000000000000)
      | 5 => orderedInterval (-6756154393 / 1000000000000) (-6756153298 / 1000000000000)
      | 6 => orderedInterval (-7574746779 / 1000000000000) (-7574746682 / 1000000000000)
      | 7 => orderedInterval (-1732043566 / 1000000000000) (-1732043517 / 1000000000000)
      | _ => orderedInterval (5096662949 / 1000000000000) (5096663344 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8047302238 / 1000000000000) (-8047292989 / 1000000000000)
      | 1 => orderedInterval (-2117189735 / 1000000000000) (-2117189540 / 1000000000000)
      | 2 => orderedInterval (-4089363369 / 1000000000000) (-4089363079 / 1000000000000)
      | 3 => orderedInterval (-9748576123 / 1000000000000) (-9748396189 / 1000000000000)
      | 4 => orderedInterval (18758119077 / 1000000000000) (18758119500 / 1000000000000)
      | 5 => orderedInterval (-5617860372 / 1000000000000) (-5617858869 / 1000000000000)
      | 6 => orderedInterval (-871258112 / 1000000000000) (-871258016 / 1000000000000)
      | 7 => orderedInterval (2853946980 / 1000000000000) (2853947032 / 1000000000000)
      | _ => orderedInterval (24471175834 / 1000000000000) (24471176469 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-4826280656 / 1000000000000) (-4826263614 / 1000000000000)
    | 1 => orderedInterval (16898337627 / 1000000000000) (16898363749 / 1000000000000)
    | 2 => orderedInterval (-1414482591 / 1000000000000) (-1414436095 / 1000000000000)
    | 3 => orderedInterval (-44284983055 / 1000000000000) (-44284891394 / 1000000000000)
    | _ => orderedInterval (15591691942 / 1000000000000) (15591884319 / 1000000000000)

theorem compactCertificate573_stateChecks0 :
    compactCertificate573.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (889 / 2)) (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1309666752683989 / 4000000000000)) (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (423519319016437 / 800000000000)) (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks1 :
    compactCertificate573.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (382157492077823 / 4000000000000)) (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1026528778618931 / 4000000000000)) (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2787225322236327 / 4000000000000)) (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks2 :
    compactCertificate573.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2053057557238751 / 4000000000000)) (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (3517949117573723 / 4000000000000)) (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2591305397591057 / 4000000000000)) (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks3 :
    compactCertificate573.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 317 12 (3975728863994111 / 4000000000000)) (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2295388129851719 / 4000000000000)) (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 324 12 (4073206516635571 / 4000000000000)) (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks4 :
    compactCertificate573.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 303 12 (3805717890293599 / 4000000000000)) (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2715939861876367 / 4000000000000)) (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3079586335856793 / 4000000000000)) (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks5 :
    compactCertificate573.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2567438023822217 / 4000000000000)) (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2268409356630557 / 4000000000000)) (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (657473447053143 / 800000000000)) (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks6 :
    compactCertificate573.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1818606155480821 / 4000000000000)) (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1541652578512781 / 4000000000000)) (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (964694602408943 / 4000000000000)) (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks7 :
    compactCertificate573.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (518815965604881 / 4000000000000)) (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1408686270697643 / 4000000000000)) (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1923440670344011 / 4000000000000)) (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_stateChecks8 :
    compactCertificate573.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (813305397591057 / 4000000000000)) (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3306041287842097 / 4000000000000)) (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2208282364890623 / 4000000000000)) (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_states : ∀ j,
    BesselStateValid (compactCertificate573.point j) (compactCertificate573.state j) :=
  compactCertificate573.statesValid_of_checks3 compactCertificate573_stateChecks0
    compactCertificate573_stateChecks1 compactCertificate573_stateChecks2
    compactCertificate573_stateChecks3 compactCertificate573_stateChecks4
    compactCertificate573_stateChecks5 compactCertificate573_stateChecks6
    compactCertificate573_stateChecks7 compactCertificate573_stateChecks8

theorem compactCertificate573_chunkChecks0_0 :
    compactCertificate573.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (889 / 2) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1309666752683989 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (423519319016437 / 800000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000)))) (orderedInterval (-9189604229 / 1000000000000) (-9189595433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (382157492077823 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1026528778618931 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2787225322236327 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000)))) (orderedInterval (-1462849614 / 1000000000000) (-1462849404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2053057557238751 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3517949117573723 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2591305397591057 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000)))) (orderedInterval (264877672 / 1000000000000) (264877704 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks0_1 :
    compactCertificate573.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3975728863994111 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2295388129851719 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4073206516635571 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000)))) (orderedInterval (-129118419 / 1000000000000) (-129111213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3805717890293599 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2715939861876367 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3079586335856793 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000)))) (orderedInterval (2949198670 / 1000000000000) (2949198724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2567438023822217 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2268409356630557 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (657473447053143 / 800000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000)))) (orderedInterval (-1259604705 / 1000000000000) (-1259604255 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks0_2 :
    compactCertificate573.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1818606155480821 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1541652578512781 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (964694602408943 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000)))) (orderedInterval (-1153443723 / 1000000000000) (-1153443610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (518815965604881 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1408686270697643 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1923440670344011 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000)))) (orderedInterval (2745041944 / 1000000000000) (2745042001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (813305397591057 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3306041287842097 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2208282364890623 / 4000000000000) 0 (IntervalRat.scale (889 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000)))) (orderedInterval (2409221748 / 1000000000000) (2409221872 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks0 :
    compactCertificate573.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate573.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate573_chunkChecks0_0
    compactCertificate573_chunkChecks0_1 compactCertificate573_chunkChecks0_2

theorem compactCertificate573_chunkChecks1_0 :
    compactCertificate573.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (889 / 2) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1309666752683989 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (423519319016437 / 800000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000)))) (orderedInterval (8479264379 / 1000000000000) (8479273253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (382157492077823 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1026528778618931 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2787225322236327 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000)))) (orderedInterval (-2202457098 / 1000000000000) (-2202457002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2053057557238751 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3517949117573723 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2591305397591057 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000)))) (orderedInterval (-1190095127 / 1000000000000) (-1190095074 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks1_1 :
    compactCertificate573.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3975728863994111 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2295388129851719 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4073206516635571 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000)))) (orderedInterval (3752820588 / 1000000000000) (3752836671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3805717890293599 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2715939861876367 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3079586335856793 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000)))) (orderedInterval (2745477156 / 1000000000000) (2745477244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2567438023822217 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2268409356630557 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (657473447053143 / 800000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000)))) (orderedInterval (2882529874 / 1000000000000) (2882530474 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks1_2 :
    compactCertificate573.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1818606155480821 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1541652578512781 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (964694602408943 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000)))) (orderedInterval (7135296283 / 1000000000000) (7135296388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (518815965604881 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1408686270697643 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1923440670344011 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000)))) (orderedInterval (1283011552 / 1000000000000) (1283011602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (813305397591057 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3306041287842097 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2208282364890623 / 4000000000000) 1 (IntervalRat.scale (889 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000)))) (orderedInterval (-5987509980 / 1000000000000) (-5987509807 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks1 :
    compactCertificate573.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate573.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate573_chunkChecks1_0
    compactCertificate573_chunkChecks1_1 compactCertificate573_chunkChecks1_2

theorem compactCertificate573_chunkChecks2_0 :
    compactCertificate573.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (889 / 2) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1309666752683989 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (423519319016437 / 800000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000)))) (orderedInterval (8780378843 / 1000000000000) (8780387829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (382157492077823 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1026528778618931 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2787225322236327 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000)))) (orderedInterval (988063491 / 1000000000000) (988063583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2053057557238751 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3517949117573723 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2591305397591057 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000)))) (orderedInterval (311454111 / 1000000000000) (311454203 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks2_1 :
    compactCertificate573.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3975728863994111 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2295388129851719 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4073206516635571 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000)))) (orderedInterval (2078801244 / 1000000000000) (2078837212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3805717890293599 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2715939861876367 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3079586335856793 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000)))) (orderedInterval (-7291268472 / 1000000000000) (-7291268327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2567438023822217 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2268409356630557 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (657473447053143 / 800000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000)))) (orderedInterval (2458590430 / 1000000000000) (2458591238 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks2_2 :
    compactCertificate573.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1818606155480821 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1541652578512781 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (964694602408943 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000)))) (orderedInterval (974177973 / 1000000000000) (974178073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (518815965604881 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1408686270697643 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1923440670344011 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000)))) (orderedInterval (-2286440497 / 1000000000000) (-2286440449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (813305397591057 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3306041287842097 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2208282364890623 / 4000000000000) 2 (IntervalRat.scale (889 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000)))) (orderedInterval (-7428239714 / 1000000000000) (-7428239457 / 1000000000000))) = true
  rfl'

theorem compactCertificate573_chunkChecks2 :
    compactCertificate573.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate573.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate573_chunkChecks2_0
    compactCertificate573_chunkChecks2_1 compactCertificate573_chunkChecks2_2

theorem compactCertificate573_chunkChecks3_0 :
    compactCertificate573.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (889 / 2) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1309666752683989 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (423519319016437 / 800000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000)))) (orderedInterval (-7739804432 / 1000000000000) (-7739795335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (382157492077823 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1026528778618931 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2787225322236327 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000)))) (orderedInterval (7823613270 / 1000000000000) (7823613398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2053057557238751 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3517949117573723 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2591305397591057 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000)))) (orderedInterval (4907917080 / 1000000000000) (4907917241 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate573_chunkChecks3_1 :
    compactCertificate573.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3975728863994111 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2295388129851719 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4073206516635571 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000)))) (orderedInterval (-29690625621 / 1000000000000) (-29690545226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3805717890293599 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2715939861876367 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3079586335856793 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000)))) (orderedInterval (-8619801563 / 1000000000000) (-8619801319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2567438023822217 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2268409356630557 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (657473447053143 / 800000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000)))) (orderedInterval (-6756154393 / 1000000000000) (-6756153298 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate573_chunkChecks3_2 :
    compactCertificate573.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1818606155480821 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1541652578512781 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (964694602408943 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000)))) (orderedInterval (-7574746779 / 1000000000000) (-7574746682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (518815965604881 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1408686270697643 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1923440670344011 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000)))) (orderedInterval (-1732043566 / 1000000000000) (-1732043517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (813305397591057 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3306041287842097 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2208282364890623 / 4000000000000) 3 (IntervalRat.scale (889 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000)))) (orderedInterval (5096662949 / 1000000000000) (5096663344 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate573_chunkChecks3 :
    compactCertificate573.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate573.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate573_chunkChecks3_0
    compactCertificate573_chunkChecks3_1 compactCertificate573_chunkChecks3_2

theorem compactCertificate573_chunkChecks4_0 :
    compactCertificate573.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (889 / 2) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27696772033 / 1000000000000) (-27696750888 / 1000000000000), orderedInterval (25820769628 / 1000000000000) (25820790773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1309666752683989 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43897313685 / 1000000000000) (43897313729 / 1000000000000), orderedInterval (4103745222 / 1000000000000) (4103745266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (423519319016437 / 800000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23506510554 / 1000000000000) (23506517092 / 1000000000000), orderedInterval (-25516841361 / 1000000000000) (-25516834823 / 1000000000000)))) (orderedInterval (-8047302238 / 1000000000000) (-8047292989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (382157492077823 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71444306747 / 1000000000000) (71444321085 / 1000000000000), orderedInterval (-39859207827 / 1000000000000) (-39859193489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1026528778618931 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9577087114 / 1000000000000) (-9577087076 / 1000000000000), orderedInterval (48895583167 / 1000000000000) (48895583206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2787225322236327 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (4755308662 / 1000000000000) (4755308663 / 1000000000000), orderedInterval (29846418441 / 1000000000000) (29846418442 / 1000000000000)))) (orderedInterval (-2117189735 / 1000000000000) (-2117189540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2053057557238751 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32450009119 / 1000000000000) (-32449970867 / 1000000000000), orderedInterval (13718544610 / 1000000000000) (13718582862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3517949117573723 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15776485606 / 1000000000000) (15776485607 / 1000000000000), orderedInterval (21784512497 / 1000000000000) (21784512498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2591305397591057 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31094289286 / 1000000000000) (31094289556 / 1000000000000), orderedInterval (3956722718 / 1000000000000) (3956722988 / 1000000000000)))) (orderedInterval (-4089363369 / 1000000000000) (-4089363079 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate573_chunkChecks4_1 :
    compactCertificate573.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3975728863994111 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23276618887 / 1000000000000) (23276658325 / 1000000000000), orderedInterval (-9946729861 / 1000000000000) (-9946690424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2295388129851719 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9180472452 / 1000000000000) (9180472465 / 1000000000000), orderedInterval (-32025316376 / 1000000000000) (-32025316364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4073206516635571 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23401529838 / 1000000000000) (23401529986 / 1000000000000), orderedInterval (8794549293 / 1000000000000) (8794549441 / 1000000000000)))) (orderedInterval (-9748576123 / 1000000000000) (-9748396189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3805717890293599 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7944377362 / 1000000000000) (-7944377361 / 1000000000000), orderedInterval (-24613018017 / 1000000000000) (-24613018016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2715939861876367 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28383130892 / 1000000000000) (28383130900 / 1000000000000), orderedInterval (11468346295 / 1000000000000) (11468346303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3079586335856793 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24066028376 / 1000000000000) (-24066028374 / 1000000000000), orderedInterval (-15723372816 / 1000000000000) (-15723372815 / 1000000000000)))) (orderedInterval (18758119077 / 1000000000000) (18758119500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2567438023822217 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30932542839 / 1000000000000) (30932552520 / 1000000000000), orderedInterval (-5941350246 / 1000000000000) (-5941340565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2268409356630557 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (22610629287 / 1000000000000) (22610634423 / 1000000000000), orderedInterval (-24745287886 / 1000000000000) (-24745282749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (657473447053143 / 800000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12610242062 / 1000000000000) (-12610242029 / 1000000000000), orderedInterval (24819112082 / 1000000000000) (24819112116 / 1000000000000)))) (orderedInterval (-5617860372 / 1000000000000) (-5617858869 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate573_chunkChecks4_2 :
    compactCertificate573.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1818606155480821 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3522434586 / 1000000000000) (3522434588 / 1000000000000), orderedInterval (-37257464075 / 1000000000000) (-37257464073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1541652578512781 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8777196669 / 1000000000000) (8777196689 / 1000000000000), orderedInterval (-39694473723 / 1000000000000) (-39694473702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (964694602408943 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2870320220 / 1000000000000) (-2870320219 / 1000000000000), orderedInterval (-51291619629 / 1000000000000) (-51291619628 / 1000000000000)))) (orderedInterval (-871258112 / 1000000000000) (-871258016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (518815965604881 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69617109975 / 1000000000000) (-69617109775 / 1000000000000), orderedInterval (8121623633 / 1000000000000) (8121623834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1408686270697643 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37857347454 / 1000000000000) (37857347455 / 1000000000000), orderedInterval (19298718918 / 1000000000000) (19298718919 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1923440670344011 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-30251206870 / 1000000000000) (-30251206869 / 1000000000000), orderedInterval (-20186925435 / 1000000000000) (-20186925434 / 1000000000000)))) (orderedInterval (2853946980 / 1000000000000) (2853947032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (813305397591057 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5162357294 / 1000000000000) (5162357306 / 1000000000000), orderedInterval (-55729692343 / 1000000000000) (-55729692330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3306041287842097 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24165921006 / 1000000000000) (-24165921003 / 1000000000000), orderedInterval (-13633033575 / 1000000000000) (-13633033572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2208282364890623 / 4000000000000) 4 (IntervalRat.scale (889 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2190268726 / 1000000000000) (-2190268725 / 1000000000000), orderedInterval (33889332550 / 1000000000000) (33889332551 / 1000000000000)))) (orderedInterval (24471175834 / 1000000000000) (24471176469 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate573_chunkChecks4 :
    compactCertificate573.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate573.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate573_chunkChecks4_0
    compactCertificate573_chunkChecks4_1 compactCertificate573_chunkChecks4_2

theorem compactCertificate573_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate573.chunkCheck r b = true :=
  compactCertificate573.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate573_chunkChecks0
    · exact compactCertificate573_chunkChecks1
    · exact compactCertificate573_chunkChecks2
    · exact compactCertificate573_chunkChecks3
    · exact compactCertificate573_chunkChecks4)

theorem compactCertificate573_coefficient0 :
    compactCertificate573.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate573_coefficient1 :
    compactCertificate573.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate573_coefficient2 :
    compactCertificate573.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate573_coefficient3 :
    compactCertificate573.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate573_coefficient4 :
    compactCertificate573.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate573_coefficients : ∀ r : Fin 5,
    compactCertificate573.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate573_coefficient0
  · exact compactCertificate573_coefficient1
  · exact compactCertificate573_coefficient2
  · exact compactCertificate573_coefficient3
  · exact compactCertificate573_coefficient4

theorem compactCertificate573_lower : (1 : ℚ) ≤ compactCertificate573.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate573, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate573_proves {t : ℝ} (ht : t ∈ compactCertificate573.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate573.proves compactCertificate573_states compactCertificate573_chunks
    compactCertificate573_coefficients compactCertificate573_lower ht

end Erdos232
