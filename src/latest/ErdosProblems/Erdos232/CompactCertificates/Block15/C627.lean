/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate627 : CompactCertificate where
  left := 498
  right := 499
  center := 997 / 2
  grid := fun i =>
    match i.val with
    | 0 => 159
    | 1 => 117
    | 2 => 189
    | 3 => 34
    | 4 => 92
    | 5 => 249
    | 6 => 183
    | 7 => 314
    | 8 => 231
    | 9 => 355
    | 10 => 205
    | 11 => 364
    | 12 => 340
    | 13 => 243
    | 14 => 275
    | 15 => 229
    | 16 => 203
    | 17 => 294
    | 18 => 162
    | 19 => 138
    | 20 => 86
    | 21 => 46
    | 22 => 126
    | 23 => 172
    | 24 => 73
    | 25 => 295
    | _ => 197
  point := fun i =>
    match i.val with
    | 0 => 997 / 2
    | 1 => 1468771375057297 / 4000000000000
    | 2 => 474970484881201 / 800000000000
    | 3 => 428583824073779 / 4000000000000
    | 4 => 1151236436763863 / 4000000000000
    | 5 => 3125830873194171 / 4000000000000
    | 6 => 2302472873528723 / 4000000000000
    | 7 => 3945326513184479 / 4000000000000
    | 8 => 2906109652866461 / 4000000000000
    | 9 => 4458719547134003 / 4000000000000
    | 10 => 2574242930778587 / 4000000000000
    | 11 => 4568039254314583 / 4000000000000
    | 12 => 4268054821847827 / 4000000000000
    | 13 => 3045885311913091 / 4000000000000
    | 14 => 3453709310291589 / 4000000000000
    | 15 => 2879342755625141 / 4000000000000
    | 16 => 2543986646299961 / 4000000000000
    | 17 => 737346486740139 / 800000000000
    | 18 => 2039539186742833 / 4000000000000
    | 19 => 1728939955879913 / 4000000000000
    | 20 => 1081890347133539 / 4000000000000
    | 21 => 581844226893213 / 4000000000000
    | 22 => 1579820260838639 / 4000000000000
    | 23 => 2157109503186703 / 4000000000000
    | 24 => 912109652866461 / 4000000000000
    | 25 => 3707675100088381 / 4000000000000
    | _ => 2476555138128179 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))
    | 1 => (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))
    | 2 => (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000))
    | 3 => (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))
    | 4 => (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))
    | 5 => (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000))
    | 6 => (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))
    | 7 => (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))
    | 8 => (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000))
    | 9 => (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))
    | 10 => (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))
    | 11 => (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000))
    | 12 => (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))
    | 13 => (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))
    | 14 => (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000))
    | 15 => (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))
    | 16 => (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))
    | 17 => (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000))
    | 18 => (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))
    | 19 => (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))
    | 20 => (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000))
    | 21 => (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))
    | 22 => (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))
    | 23 => (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000))
    | 24 => (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))
    | 25 => (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))
    | _ => (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1755751555 / 1000000000000) (1755751594 / 1000000000000)
      | 1 => orderedInterval (-1498581459 / 1000000000000) (-1498581370 / 1000000000000)
      | 2 => orderedInterval (-1193462714 / 1000000000000) (-1193462613 / 1000000000000)
      | 3 => orderedInterval (-2163682611 / 1000000000000) (-2163682390 / 1000000000000)
      | 4 => orderedInterval (2681564251 / 1000000000000) (2681573263 / 1000000000000)
      | 5 => orderedInterval (-2421179265 / 1000000000000) (-2421176100 / 1000000000000)
      | 6 => orderedInterval (-3104462566 / 1000000000000) (-3104461809 / 1000000000000)
      | 7 => orderedInterval (-357769108 / 1000000000000) (-357769039 / 1000000000000)
      | _ => orderedInterval (7033423420 / 1000000000000) (7033423578 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15755612433 / 1000000000000) (-15755612390 / 1000000000000)
      | 1 => orderedInterval (4003193123 / 1000000000000) (4003193208 / 1000000000000)
      | 2 => orderedInterval (-1191293089 / 1000000000000) (-1191292935 / 1000000000000)
      | 3 => orderedInterval (12106474519 / 1000000000000) (12106474983 / 1000000000000)
      | 4 => orderedInterval (-2367009348 / 1000000000000) (-2366995576 / 1000000000000)
      | 5 => orderedInterval (1640027414 / 1000000000000) (1640032209 / 1000000000000)
      | 6 => orderedInterval (-300979009 / 1000000000000) (-300978256 / 1000000000000)
      | 7 => orderedInterval (-3388819289 / 1000000000000) (-3388819231 / 1000000000000)
      | _ => orderedInterval (6070327798 / 1000000000000) (6070328002 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1254546810 / 1000000000000) (-1254546761 / 1000000000000)
      | 1 => orderedInterval (334450092 / 1000000000000) (334450196 / 1000000000000)
      | 2 => orderedInterval (3394231275 / 1000000000000) (3394231516 / 1000000000000)
      | 3 => orderedInterval (8919295551 / 1000000000000) (8919296554 / 1000000000000)
      | 4 => orderedInterval (-6610058714 / 1000000000000) (-6610037637 / 1000000000000)
      | 5 => orderedInterval (5188597463 / 1000000000000) (5188604991 / 1000000000000)
      | 6 => orderedInterval (4613621496 / 1000000000000) (4613622253 / 1000000000000)
      | 7 => orderedInterval (-833232711 / 1000000000000) (-833232655 / 1000000000000)
      | _ => orderedInterval (-13934082598 / 1000000000000) (-13934082307 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16346776272 / 1000000000000) (16346776329 / 1000000000000)
      | 1 => orderedInterval (-8113220289 / 1000000000000) (-8113220142 / 1000000000000)
      | 2 => orderedInterval (4721567848 / 1000000000000) (4721568230 / 1000000000000)
      | 3 => orderedInterval (-71472399003 / 1000000000000) (-71472396794 / 1000000000000)
      | 4 => orderedInterval (7382605111 / 1000000000000) (7382637332 / 1000000000000)
      | 5 => orderedInterval (-3488156486 / 1000000000000) (-3488144289 / 1000000000000)
      | 6 => orderedInterval (126351136 / 1000000000000) (126351898 / 1000000000000)
      | 7 => orderedInterval (3641470566 / 1000000000000) (3641470623 / 1000000000000)
      | _ => orderedInterval (-14016364077 / 1000000000000) (-14016363632 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (492260697 / 1000000000000) (492260762 / 1000000000000)
      | 1 => orderedInterval (-215830242 / 1000000000000) (-215830021 / 1000000000000)
      | 2 => orderedInterval (-10577825374 / 1000000000000) (-10577824754 / 1000000000000)
      | 3 => orderedInterval (-43328271758 / 1000000000000) (-43328266832 / 1000000000000)
      | 4 => orderedInterval (17004848423 / 1000000000000) (17004897762 / 1000000000000)
      | 5 => orderedInterval (-12518166928 / 1000000000000) (-12518146551 / 1000000000000)
      | 6 => orderedInterval (-5373755388 / 1000000000000) (-5373754616 / 1000000000000)
      | 7 => orderedInterval (1048733160 / 1000000000000) (1048733220 / 1000000000000)
      | _ => orderedInterval (32844343502 / 1000000000000) (32844344214 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (731601503 / 1000000000000) (731615114 / 1000000000000)
    | 1 => orderedInterval (816309686 / 1000000000000) (816330014 / 1000000000000)
    | 2 => orderedInterval (-181724956 / 1000000000000) (-181693850 / 1000000000000)
    | 3 => orderedInterval (-64871368922 / 1000000000000) (-64871320445 / 1000000000000)
    | _ => orderedInterval (-20623663908 / 1000000000000) (-20623586816 / 1000000000000)

theorem compactCertificate627_stateChecks0 :
    compactCertificate627.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (997 / 2)) (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1468771375057297 / 4000000000000)) (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (474970484881201 / 800000000000)) (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks1 :
    compactCertificate627.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (428583824073779 / 4000000000000)) (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1151236436763863 / 4000000000000)) (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3125830873194171 / 4000000000000)) (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks2 :
    compactCertificate627.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2302472873528723 / 4000000000000)) (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 314 12 (3945326513184479 / 4000000000000)) (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2906109652866461 / 4000000000000)) (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks3 :
    compactCertificate627.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 355 12 (4458719547134003 / 4000000000000)) (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2574242930778587 / 4000000000000)) (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 364 12 (4568039254314583 / 4000000000000)) (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks4 :
    compactCertificate627.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 340 12 (4268054821847827 / 4000000000000)) (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3045885311913091 / 4000000000000)) (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3453709310291589 / 4000000000000)) (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks5 :
    compactCertificate627.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2879342755625141 / 4000000000000)) (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2543986646299961 / 4000000000000)) (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (737346486740139 / 800000000000)) (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks6 :
    compactCertificate627.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2039539186742833 / 4000000000000)) (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1728939955879913 / 4000000000000)) (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1081890347133539 / 4000000000000)) (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks7 :
    compactCertificate627.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (581844226893213 / 4000000000000)) (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1579820260838639 / 4000000000000)) (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2157109503186703 / 4000000000000)) (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_stateChecks8 :
    compactCertificate627.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (912109652866461 / 4000000000000)) (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (3707675100088381 / 4000000000000)) (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2476555138128179 / 4000000000000)) (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_states : ∀ j,
    BesselStateValid (compactCertificate627.point j) (compactCertificate627.state j) :=
  compactCertificate627.statesValid_of_checks3 compactCertificate627_stateChecks0
    compactCertificate627_stateChecks1 compactCertificate627_stateChecks2
    compactCertificate627_stateChecks3 compactCertificate627_stateChecks4
    compactCertificate627_stateChecks5 compactCertificate627_stateChecks6
    compactCertificate627_stateChecks7 compactCertificate627_stateChecks8

theorem compactCertificate627_chunkChecks0_0 :
    compactCertificate627.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (997 / 2) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1468771375057297 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (474970484881201 / 800000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000)))) (orderedInterval (1755751555 / 1000000000000) (1755751594 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (428583824073779 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1151236436763863 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3125830873194171 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000)))) (orderedInterval (-1498581459 / 1000000000000) (-1498581370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2302472873528723 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3945326513184479 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2906109652866461 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000)))) (orderedInterval (-1193462714 / 1000000000000) (-1193462613 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks0_1 :
    compactCertificate627.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4458719547134003 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2574242930778587 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4568039254314583 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000)))) (orderedInterval (-2163682611 / 1000000000000) (-2163682390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4268054821847827 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3045885311913091 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3453709310291589 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000)))) (orderedInterval (2681564251 / 1000000000000) (2681573263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2879342755625141 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2543986646299961 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (737346486740139 / 800000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000)))) (orderedInterval (-2421179265 / 1000000000000) (-2421176100 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks0_2 :
    compactCertificate627.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2039539186742833 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1728939955879913 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1081890347133539 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000)))) (orderedInterval (-3104462566 / 1000000000000) (-3104461809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (581844226893213 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1579820260838639 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2157109503186703 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000)))) (orderedInterval (-357769108 / 1000000000000) (-357769039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (912109652866461 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3707675100088381 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2476555138128179 / 4000000000000) 0 (IntervalRat.scale (997 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000)))) (orderedInterval (7033423420 / 1000000000000) (7033423578 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks0 :
    compactCertificate627.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate627.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate627_chunkChecks0_0
    compactCertificate627_chunkChecks0_1 compactCertificate627_chunkChecks0_2

theorem compactCertificate627_chunkChecks1_0 :
    compactCertificate627.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (997 / 2) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1468771375057297 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (474970484881201 / 800000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000)))) (orderedInterval (-15755612433 / 1000000000000) (-15755612390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (428583824073779 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1151236436763863 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3125830873194171 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000)))) (orderedInterval (4003193123 / 1000000000000) (4003193208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2302472873528723 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3945326513184479 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2906109652866461 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000)))) (orderedInterval (-1191293089 / 1000000000000) (-1191292935 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks1_1 :
    compactCertificate627.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4458719547134003 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2574242930778587 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4568039254314583 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000)))) (orderedInterval (12106474519 / 1000000000000) (12106474983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4268054821847827 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3045885311913091 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3453709310291589 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000)))) (orderedInterval (-2367009348 / 1000000000000) (-2366995576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2879342755625141 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2543986646299961 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (737346486740139 / 800000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000)))) (orderedInterval (1640027414 / 1000000000000) (1640032209 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks1_2 :
    compactCertificate627.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2039539186742833 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1728939955879913 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1081890347133539 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000)))) (orderedInterval (-300979009 / 1000000000000) (-300978256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (581844226893213 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1579820260838639 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2157109503186703 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000)))) (orderedInterval (-3388819289 / 1000000000000) (-3388819231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (912109652866461 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3707675100088381 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2476555138128179 / 4000000000000) 1 (IntervalRat.scale (997 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000)))) (orderedInterval (6070327798 / 1000000000000) (6070328002 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks1 :
    compactCertificate627.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate627.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate627_chunkChecks1_0
    compactCertificate627_chunkChecks1_1 compactCertificate627_chunkChecks1_2

theorem compactCertificate627_chunkChecks2_0 :
    compactCertificate627.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (997 / 2) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1468771375057297 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (474970484881201 / 800000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000)))) (orderedInterval (-1254546810 / 1000000000000) (-1254546761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (428583824073779 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1151236436763863 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3125830873194171 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000)))) (orderedInterval (334450092 / 1000000000000) (334450196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2302472873528723 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3945326513184479 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2906109652866461 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000)))) (orderedInterval (3394231275 / 1000000000000) (3394231516 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks2_1 :
    compactCertificate627.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4458719547134003 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2574242930778587 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4568039254314583 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000)))) (orderedInterval (8919295551 / 1000000000000) (8919296554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4268054821847827 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3045885311913091 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3453709310291589 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000)))) (orderedInterval (-6610058714 / 1000000000000) (-6610037637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2879342755625141 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2543986646299961 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (737346486740139 / 800000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000)))) (orderedInterval (5188597463 / 1000000000000) (5188604991 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks2_2 :
    compactCertificate627.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2039539186742833 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1728939955879913 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1081890347133539 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000)))) (orderedInterval (4613621496 / 1000000000000) (4613622253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (581844226893213 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1579820260838639 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2157109503186703 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000)))) (orderedInterval (-833232711 / 1000000000000) (-833232655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (912109652866461 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3707675100088381 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2476555138128179 / 4000000000000) 2 (IntervalRat.scale (997 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000)))) (orderedInterval (-13934082598 / 1000000000000) (-13934082307 / 1000000000000))) = true
  rfl'

theorem compactCertificate627_chunkChecks2 :
    compactCertificate627.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate627.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate627_chunkChecks2_0
    compactCertificate627_chunkChecks2_1 compactCertificate627_chunkChecks2_2

theorem compactCertificate627_chunkChecks3_0 :
    compactCertificate627.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (997 / 2) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1468771375057297 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (474970484881201 / 800000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000)))) (orderedInterval (16346776272 / 1000000000000) (16346776329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (428583824073779 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1151236436763863 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3125830873194171 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000)))) (orderedInterval (-8113220289 / 1000000000000) (-8113220142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2302472873528723 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3945326513184479 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2906109652866461 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000)))) (orderedInterval (4721567848 / 1000000000000) (4721568230 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate627_chunkChecks3_1 :
    compactCertificate627.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4458719547134003 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2574242930778587 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4568039254314583 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000)))) (orderedInterval (-71472399003 / 1000000000000) (-71472396794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4268054821847827 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3045885311913091 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3453709310291589 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000)))) (orderedInterval (7382605111 / 1000000000000) (7382637332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2879342755625141 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2543986646299961 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (737346486740139 / 800000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000)))) (orderedInterval (-3488156486 / 1000000000000) (-3488144289 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate627_chunkChecks3_2 :
    compactCertificate627.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2039539186742833 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1728939955879913 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1081890347133539 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000)))) (orderedInterval (126351136 / 1000000000000) (126351898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (581844226893213 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1579820260838639 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2157109503186703 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000)))) (orderedInterval (3641470566 / 1000000000000) (3641470623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (912109652866461 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3707675100088381 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2476555138128179 / 4000000000000) 3 (IntervalRat.scale (997 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000)))) (orderedInterval (-14016364077 / 1000000000000) (-14016363632 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate627_chunkChecks3 :
    compactCertificate627.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate627.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate627_chunkChecks3_0
    compactCertificate627_chunkChecks3_1 compactCertificate627_chunkChecks3_2

theorem compactCertificate627_chunkChecks4_0 :
    compactCertificate627.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (997 / 2) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (8080367109 / 1000000000000) (8080367119 / 1000000000000), orderedInterval (-34818720889 / 1000000000000) (-34818720879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1468771375057297 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16656997483 / 1000000000000) (-16656997482 / 1000000000000), orderedInterval (-38138729552 / 1000000000000) (-38138729551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (474970484881201 / 800000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22014094783 / 1000000000000) (-22014094782 / 1000000000000), orderedInterval (-24222913128 / 1000000000000) (-24222913127 / 1000000000000)))) (orderedInterval (492260697 / 1000000000000) (492260762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (428583824073779 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69247414826 / 1000000000000) (69247414827 / 1000000000000), orderedInterval (33534925950 / 1000000000000) (33534925951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1151236436763863 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-19710722718 / 1000000000000) (-19710721935 / 1000000000000), orderedInterval (42736010614 / 1000000000000) (42736011398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3125830873194171 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (388568183 / 1000000000000) (388568184 / 1000000000000), orderedInterval (-28539798187 / 1000000000000) (-28539798186 / 1000000000000)))) (orderedInterval (-215830242 / 1000000000000) (-215830021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2302472873528723 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33152871706 / 1000000000000) (-33152871391 / 1000000000000), orderedInterval (-2590823475 / 1000000000000) (-2590823160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3945326513184479 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15512395680 / 1000000000000) (15512395681 / 1000000000000), orderedInterval (20111965188 / 1000000000000) (20111965189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2906109652866461 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29584473397 / 1000000000000) (-29584470400 / 1000000000000), orderedInterval (1024842277 / 1000000000000) (1024845274 / 1000000000000)))) (orderedInterval (-10577825374 / 1000000000000) (-10577824754 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate627_chunkChecks4_1 :
    compactCertificate627.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4458719547134003 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4742702263 / 1000000000000) (-4742702262 / 1000000000000), orderedInterval (-23420729684 / 1000000000000) (-23420729683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2574242930778587 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9877036632 / 1000000000000) (-9877036631 / 1000000000000), orderedInterval (-29852988377 / 1000000000000) (-29852988376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4568039254314583 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16000717751 / 1000000000000) (-16000717585 / 1000000000000), orderedInterval (17368821115 / 1000000000000) (17368821281 / 1000000000000)))) (orderedInterval (-43328271758 / 1000000000000) (-43328266832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4268054821847827 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8203712486 / 1000000000000) (-8203712485 / 1000000000000), orderedInterval (23011149027 / 1000000000000) (23011149028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3045885311913091 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26397261254 / 1000000000000) (26397355928 / 1000000000000), orderedInterval (-11816573604 / 1000000000000) (-11816478931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3453709310291589 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7363050223 / 1000000000000) (-7363050222 / 1000000000000), orderedInterval (-26131970429 / 1000000000000) (-26131970428 / 1000000000000)))) (orderedInterval (17004848423 / 1000000000000) (17004897762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2879342755625141 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27676521001 / 1000000000000) (-27676520988 / 1000000000000), orderedInterval (-10862227268 / 1000000000000) (-10862227256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2543986646299961 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25943980142 / 1000000000000) (25944011748 / 1000000000000), orderedInterval (-18128108723 / 1000000000000) (-18128077117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (737346486740139 / 800000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24093560909 / 1000000000000) (-24093509825 / 1000000000000), orderedInterval (10511417351 / 1000000000000) (10511468436 / 1000000000000)))) (orderedInterval (-12518166928 / 1000000000000) (-12518146551 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate627_chunkChecks4_2 :
    compactCertificate627.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2039539186742833 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34877120161 / 1000000000000) (34877123782 / 1000000000000), orderedInterval (-5703584376 / 1000000000000) (-5703580756 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1728939955879913 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19058778220 / 1000000000000) (-19058777291 / 1000000000000), orderedInterval (33332993442 / 1000000000000) (33332994371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1081890347133539 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42801057697 / 1000000000000) (42801057698 / 1000000000000), orderedInterval (22763785500 / 1000000000000) (22763785501 / 1000000000000)))) (orderedInterval (-5373755388 / 1000000000000) (-5373754616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (581844226893213 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65294153474 / 1000000000000) (65294153896 / 1000000000000), orderedInterval (-10864642722 / 1000000000000) (-10864642300 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1579820260838639 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4029202263 / 1000000000000) (-4029202260 / 1000000000000), orderedInterval (39950636080 / 1000000000000) (39950636083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2157109503186703 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9870776517 / 1000000000000) (-9870776498 / 1000000000000), orderedInterval (32919233013 / 1000000000000) (32919233032 / 1000000000000)))) (orderedInterval (1048733160 / 1000000000000) (1048733220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (912109652866461 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (26437357031 / 1000000000000) (26437360202 / 1000000000000), orderedInterval (-45806476136 / 1000000000000) (-45806472965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3707675100088381 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21073848857 / 1000000000000) (-21073848855 / 1000000000000), orderedInterval (-15567649150 / 1000000000000) (-15567649148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2476555138128179 / 4000000000000) 4 (IntervalRat.scale (997 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27493989083 / 1000000000000) (-27493989082 / 1000000000000), orderedInterval (-16479759135 / 1000000000000) (-16479759133 / 1000000000000)))) (orderedInterval (32844343502 / 1000000000000) (32844344214 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate627_chunkChecks4 :
    compactCertificate627.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate627.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate627_chunkChecks4_0
    compactCertificate627_chunkChecks4_1 compactCertificate627_chunkChecks4_2

theorem compactCertificate627_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate627.chunkCheck r b = true :=
  compactCertificate627.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate627_chunkChecks0
    · exact compactCertificate627_chunkChecks1
    · exact compactCertificate627_chunkChecks2
    · exact compactCertificate627_chunkChecks3
    · exact compactCertificate627_chunkChecks4)

theorem compactCertificate627_coefficient0 :
    compactCertificate627.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate627_coefficient1 :
    compactCertificate627.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate627_coefficient2 :
    compactCertificate627.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate627_coefficient3 :
    compactCertificate627.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate627_coefficient4 :
    compactCertificate627.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate627_coefficients : ∀ r : Fin 5,
    compactCertificate627.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate627_coefficient0
  · exact compactCertificate627_coefficient1
  · exact compactCertificate627_coefficient2
  · exact compactCertificate627_coefficient3
  · exact compactCertificate627_coefficient4

theorem compactCertificate627_lower : (1 : ℚ) ≤ compactCertificate627.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate627, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate627_proves {t : ℝ} (ht : t ∈ compactCertificate627.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate627.proves compactCertificate627_states compactCertificate627_chunks
    compactCertificate627_coefficients compactCertificate627_lower ht

end Erdos232
