/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate398 : CompactCertificate where
  left := 269
  right := 270
  center := 539 / 2
  grid := fun i =>
    match i.val with
    | 0 => 86
    | 1 => 63
    | 2 => 102
    | 3 => 18
    | 4 => 50
    | 5 => 135
    | 6 => 99
    | 7 => 170
    | 8 => 125
    | 9 => 192
    | 10 => 111
    | 11 => 197
    | 12 => 184
    | 13 => 131
    | 14 => 149
    | 15 => 124
    | 16 => 110
    | 17 => 159
    | 18 => 88
    | 19 => 74
    | 20 => 47
    | 21 => 25
    | 22 => 68
    | 23 => 93
    | 24 => 39
    | 25 => 160
    | _ => 107
  point := fun i =>
    match i.val with
    | 0 => 539 / 2
    | 1 => 794049920918639 / 4000000000000
    | 2 => 256779429639887 / 800000000000
    | 3 => 231701786535373 / 4000000000000
    | 4 => 622383590186281 / 4000000000000
    | 5 => 1689892518206277 / 4000000000000
    | 6 => 1244767180373101 / 4000000000000
    | 7 => 2132929779946273 / 4000000000000
    | 8 => 1571106422161507 / 4000000000000
    | 9 => 2410481279744461 / 4000000000000
    | 10 => 1391692015736869 / 4000000000000
    | 11 => 2469581903786921 / 4000000000000
    | 12 => 2307403760256749 / 4000000000000
    | 13 => 1646672199720317 / 4000000000000
    | 14 => 1867150770558843 / 4000000000000
    | 15 => 1556635652238667 / 4000000000000
    | 16 => 1375334806776007 / 4000000000000
    | 17 => 398625633252693 / 800000000000
    | 18 => 1102619480094671 / 4000000000000
    | 19 => 934702744452631 / 4000000000000
    | 20 => 584893577838493 / 4000000000000
    | 21 => 314557711429731 / 4000000000000
    | 22 => 854085376722193 / 4000000000000
    | 23 => 1166180563909361 / 4000000000000
    | 24 => 493106422161507 / 4000000000000
    | 25 => 2004450229636547 / 4000000000000
    | _ => 1338879859028173 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))
    | 1 => (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))
    | 2 => (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000))
    | 3 => (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))
    | 4 => (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))
    | 5 => (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000))
    | 6 => (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))
    | 7 => (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))
    | 8 => (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000))
    | 9 => (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))
    | 10 => (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))
    | 11 => (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000))
    | 12 => (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))
    | 13 => (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))
    | 14 => (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000))
    | 15 => (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))
    | 16 => (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))
    | 17 => (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000))
    | 18 => (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))
    | 19 => (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))
    | 20 => (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000))
    | 21 => (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))
    | 22 => (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))
    | 23 => (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000))
    | 24 => (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))
    | 25 => (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))
    | _ => (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4087637256 / 1000000000000) (4087637276 / 1000000000000)
      | 1 => orderedInterval (-4534111965 / 1000000000000) (-4534108354 / 1000000000000)
      | 2 => orderedInterval (-682414025 / 1000000000000) (-682414009 / 1000000000000)
      | 3 => orderedInterval (1755082762 / 1000000000000) (1755083282 / 1000000000000)
      | 4 => orderedInterval (-2774040307 / 1000000000000) (-2774040268 / 1000000000000)
      | 5 => orderedInterval (2583049263 / 1000000000000) (2583055572 / 1000000000000)
      | 6 => orderedInterval (-1256191082 / 1000000000000) (-1256189819 / 1000000000000)
      | 7 => orderedInterval (1084838299 / 1000000000000) (1084838332 / 1000000000000)
      | _ => orderedInterval (-3362387935 / 1000000000000) (-3362385945 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19851759109 / 1000000000000) (19851759131 / 1000000000000)
      | 1 => orderedInterval (4009317271 / 1000000000000) (4009321567 / 1000000000000)
      | 2 => orderedInterval (-3026831622 / 1000000000000) (-3026831595 / 1000000000000)
      | 3 => orderedInterval (-24607766194 / 1000000000000) (-24607765026 / 1000000000000)
      | 4 => orderedInterval (-4399280977 / 1000000000000) (-4399280913 / 1000000000000)
      | 5 => orderedInterval (-2717554719 / 1000000000000) (-2717546662 / 1000000000000)
      | 6 => orderedInterval (-7759989160 / 1000000000000) (-7759988239 / 1000000000000)
      | 7 => orderedInterval (3364601509 / 1000000000000) (3364601539 / 1000000000000)
      | _ => orderedInterval (4197362260 / 1000000000000) (4197365174 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5456721855 / 1000000000000) (-5456721830 / 1000000000000)
      | 1 => orderedInterval (5654844399 / 1000000000000) (5654850505 / 1000000000000)
      | 2 => orderedInterval (1359368661 / 1000000000000) (1359368709 / 1000000000000)
      | 3 => orderedInterval (-9332882920 / 1000000000000) (-9332880274 / 1000000000000)
      | 4 => orderedInterval (6005471272 / 1000000000000) (6005471379 / 1000000000000)
      | 5 => orderedInterval (-4981948377 / 1000000000000) (-4981938054 / 1000000000000)
      | 6 => orderedInterval (1519446540 / 1000000000000) (1519447250 / 1000000000000)
      | 7 => orderedInterval (-310134652 / 1000000000000) (-310134622 / 1000000000000)
      | _ => orderedInterval (777987352 / 1000000000000) (777991808 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20190327427 / 1000000000000) (-20190327397 / 1000000000000)
      | 1 => orderedInterval (-7343642636 / 1000000000000) (-7343633409 / 1000000000000)
      | 2 => orderedInterval (10195183753 / 1000000000000) (10195183839 / 1000000000000)
      | 3 => orderedInterval (111399225027 / 1000000000000) (111399231041 / 1000000000000)
      | 4 => orderedInterval (12695533473 / 1000000000000) (12695533658 / 1000000000000)
      | 5 => orderedInterval (6891243560 / 1000000000000) (6891256757 / 1000000000000)
      | 6 => orderedInterval (7715117402 / 1000000000000) (7715117971 / 1000000000000)
      | 7 => orderedInterval (-4019160556 / 1000000000000) (-4019160526 / 1000000000000)
      | _ => orderedInterval (1030494541 / 1000000000000) (1030501613 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7162889592 / 1000000000000) (7162889626 / 1000000000000)
      | 1 => orderedInterval (-12708857981 / 1000000000000) (-12708843675 / 1000000000000)
      | 2 => orderedInterval (-2542347153 / 1000000000000) (-2542346994 / 1000000000000)
      | 3 => orderedInterval (50029758246 / 1000000000000) (50029771968 / 1000000000000)
      | 4 => orderedInterval (-11754453227 / 1000000000000) (-11754452900 / 1000000000000)
      | 5 => orderedInterval (10659223077 / 1000000000000) (10659240012 / 1000000000000)
      | 6 => orderedInterval (-1304141995 / 1000000000000) (-1304141521 / 1000000000000)
      | 7 => orderedInterval (524102725 / 1000000000000) (524102757 / 1000000000000)
      | _ => orderedInterval (12082041550 / 1000000000000) (12082053223 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3098537734 / 1000000000000) (-3098523933 / 1000000000000)
    | 1 => orderedInterval (-11088382523 / 1000000000000) (-11088365024 / 1000000000000)
    | 2 => orderedInterval (-4764569580 / 1000000000000) (-4764545129 / 1000000000000)
    | 3 => orderedInterval (118373667137 / 1000000000000) (118373703547 / 1000000000000)
    | _ => orderedInterval (52148214834 / 1000000000000) (52148272496 / 1000000000000)

theorem compactCertificate398_stateChecks0 :
    compactCertificate398.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (539 / 2)) (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (794049920918639 / 4000000000000)) (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (256779429639887 / 800000000000)) (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks1 :
    compactCertificate398.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (231701786535373 / 4000000000000)) (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (622383590186281 / 4000000000000)) (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1689892518206277 / 4000000000000)) (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks2 :
    compactCertificate398.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1244767180373101 / 4000000000000)) (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2132929779946273 / 4000000000000)) (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1571106422161507 / 4000000000000)) (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks3 :
    compactCertificate398.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2410481279744461 / 4000000000000)) (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1391692015736869 / 4000000000000)) (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2469581903786921 / 4000000000000)) (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks4 :
    compactCertificate398.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2307403760256749 / 4000000000000)) (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1646672199720317 / 4000000000000)) (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1867150770558843 / 4000000000000)) (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks5 :
    compactCertificate398.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1556635652238667 / 4000000000000)) (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1375334806776007 / 4000000000000)) (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (398625633252693 / 800000000000)) (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks6 :
    compactCertificate398.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1102619480094671 / 4000000000000)) (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (934702744452631 / 4000000000000)) (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584893577838493 / 4000000000000)) (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks7 :
    compactCertificate398.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (314557711429731 / 4000000000000)) (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (854085376722193 / 4000000000000)) (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1166180563909361 / 4000000000000)) (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_stateChecks8 :
    compactCertificate398.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (493106422161507 / 4000000000000)) (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2004450229636547 / 4000000000000)) (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1338879859028173 / 4000000000000)) (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_states : ∀ j,
    BesselStateValid (compactCertificate398.point j) (compactCertificate398.state j) :=
  compactCertificate398.statesValid_of_checks3 compactCertificate398_stateChecks0
    compactCertificate398_stateChecks1 compactCertificate398_stateChecks2
    compactCertificate398_stateChecks3 compactCertificate398_stateChecks4
    compactCertificate398_stateChecks5 compactCertificate398_stateChecks6
    compactCertificate398_stateChecks7 compactCertificate398_stateChecks8

theorem compactCertificate398_chunkChecks0_0 :
    compactCertificate398.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (539 / 2) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (794049920918639 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (256779429639887 / 800000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000)))) (orderedInterval (4087637256 / 1000000000000) (4087637276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (231701786535373 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (622383590186281 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1689892518206277 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000)))) (orderedInterval (-4534111965 / 1000000000000) (-4534108354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1244767180373101 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2132929779946273 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1571106422161507 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000)))) (orderedInterval (-682414025 / 1000000000000) (-682414009 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks0_1 :
    compactCertificate398.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2410481279744461 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1391692015736869 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2469581903786921 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000)))) (orderedInterval (1755082762 / 1000000000000) (1755083282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2307403760256749 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1646672199720317 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1867150770558843 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000)))) (orderedInterval (-2774040307 / 1000000000000) (-2774040268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1556635652238667 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1375334806776007 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (398625633252693 / 800000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000)))) (orderedInterval (2583049263 / 1000000000000) (2583055572 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks0_2 :
    compactCertificate398.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1102619480094671 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (934702744452631 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (584893577838493 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000)))) (orderedInterval (-1256191082 / 1000000000000) (-1256189819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (314557711429731 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (854085376722193 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1166180563909361 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000)))) (orderedInterval (1084838299 / 1000000000000) (1084838332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (493106422161507 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2004450229636547 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1338879859028173 / 4000000000000) 0 (IntervalRat.scale (539 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000)))) (orderedInterval (-3362387935 / 1000000000000) (-3362385945 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks0 :
    compactCertificate398.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate398.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate398_chunkChecks0_0
    compactCertificate398_chunkChecks0_1 compactCertificate398_chunkChecks0_2

theorem compactCertificate398_chunkChecks1_0 :
    compactCertificate398.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (539 / 2) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (794049920918639 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (256779429639887 / 800000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000)))) (orderedInterval (19851759109 / 1000000000000) (19851759131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (231701786535373 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (622383590186281 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1689892518206277 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000)))) (orderedInterval (4009317271 / 1000000000000) (4009321567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1244767180373101 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2132929779946273 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1571106422161507 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000)))) (orderedInterval (-3026831622 / 1000000000000) (-3026831595 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks1_1 :
    compactCertificate398.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2410481279744461 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1391692015736869 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2469581903786921 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000)))) (orderedInterval (-24607766194 / 1000000000000) (-24607765026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2307403760256749 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1646672199720317 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1867150770558843 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000)))) (orderedInterval (-4399280977 / 1000000000000) (-4399280913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1556635652238667 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1375334806776007 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (398625633252693 / 800000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000)))) (orderedInterval (-2717554719 / 1000000000000) (-2717546662 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks1_2 :
    compactCertificate398.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1102619480094671 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (934702744452631 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (584893577838493 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000)))) (orderedInterval (-7759989160 / 1000000000000) (-7759988239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (314557711429731 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (854085376722193 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1166180563909361 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000)))) (orderedInterval (3364601509 / 1000000000000) (3364601539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (493106422161507 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2004450229636547 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1338879859028173 / 4000000000000) 1 (IntervalRat.scale (539 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000)))) (orderedInterval (4197362260 / 1000000000000) (4197365174 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks1 :
    compactCertificate398.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate398.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate398_chunkChecks1_0
    compactCertificate398_chunkChecks1_1 compactCertificate398_chunkChecks1_2

theorem compactCertificate398_chunkChecks2_0 :
    compactCertificate398.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (539 / 2) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (794049920918639 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (256779429639887 / 800000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000)))) (orderedInterval (-5456721855 / 1000000000000) (-5456721830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (231701786535373 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (622383590186281 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1689892518206277 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000)))) (orderedInterval (5654844399 / 1000000000000) (5654850505 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1244767180373101 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2132929779946273 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1571106422161507 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000)))) (orderedInterval (1359368661 / 1000000000000) (1359368709 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks2_1 :
    compactCertificate398.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2410481279744461 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1391692015736869 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2469581903786921 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000)))) (orderedInterval (-9332882920 / 1000000000000) (-9332880274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2307403760256749 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1646672199720317 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1867150770558843 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000)))) (orderedInterval (6005471272 / 1000000000000) (6005471379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1556635652238667 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1375334806776007 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (398625633252693 / 800000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000)))) (orderedInterval (-4981948377 / 1000000000000) (-4981938054 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks2_2 :
    compactCertificate398.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1102619480094671 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (934702744452631 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (584893577838493 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000)))) (orderedInterval (1519446540 / 1000000000000) (1519447250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (314557711429731 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (854085376722193 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1166180563909361 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000)))) (orderedInterval (-310134652 / 1000000000000) (-310134622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (493106422161507 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2004450229636547 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1338879859028173 / 4000000000000) 2 (IntervalRat.scale (539 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000)))) (orderedInterval (777987352 / 1000000000000) (777991808 / 1000000000000))) = true
  rfl'

theorem compactCertificate398_chunkChecks2 :
    compactCertificate398.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate398.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate398_chunkChecks2_0
    compactCertificate398_chunkChecks2_1 compactCertificate398_chunkChecks2_2

theorem compactCertificate398_chunkChecks3_0 :
    compactCertificate398.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (539 / 2) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (794049920918639 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (256779429639887 / 800000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000)))) (orderedInterval (-20190327427 / 1000000000000) (-20190327397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (231701786535373 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (622383590186281 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1689892518206277 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000)))) (orderedInterval (-7343642636 / 1000000000000) (-7343633409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1244767180373101 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2132929779946273 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1571106422161507 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000)))) (orderedInterval (10195183753 / 1000000000000) (10195183839 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate398_chunkChecks3_1 :
    compactCertificate398.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2410481279744461 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1391692015736869 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2469581903786921 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000)))) (orderedInterval (111399225027 / 1000000000000) (111399231041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2307403760256749 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1646672199720317 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1867150770558843 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000)))) (orderedInterval (12695533473 / 1000000000000) (12695533658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1556635652238667 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1375334806776007 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (398625633252693 / 800000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000)))) (orderedInterval (6891243560 / 1000000000000) (6891256757 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate398_chunkChecks3_2 :
    compactCertificate398.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1102619480094671 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (934702744452631 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (584893577838493 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000)))) (orderedInterval (7715117402 / 1000000000000) (7715117971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (314557711429731 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (854085376722193 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1166180563909361 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000)))) (orderedInterval (-4019160556 / 1000000000000) (-4019160526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (493106422161507 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2004450229636547 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1338879859028173 / 4000000000000) 3 (IntervalRat.scale (539 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000)))) (orderedInterval (1030494541 / 1000000000000) (1030501613 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate398_chunkChecks3 :
    compactCertificate398.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate398.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate398_chunkChecks3_0
    compactCertificate398_chunkChecks3_1 compactCertificate398_chunkChecks3_2

theorem compactCertificate398_chunkChecks4_0 :
    compactCertificate398.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (539 / 2) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5237255903 / 1000000000000) (5237255904 / 1000000000000), orderedInterval (48310058065 / 1000000000000) (48310058066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (794049920918639 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55568791912 / 1000000000000) (-55568791908 / 1000000000000), orderedInterval (-10771079339 / 1000000000000) (-10771079335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (256779429639887 / 800000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43106962535 / 1000000000000) (43106962539 / 1000000000000), orderedInterval (11121492432 / 1000000000000) (11121492436 / 1000000000000)))) (orderedInterval (7162889592 / 1000000000000) (7162889626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (231701786535373 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87155129467 / 1000000000000) (87155156280 / 1000000000000), orderedInterval (-59011632817 / 1000000000000) (-59011606004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (622383590186281 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41165082974 / 1000000000000) (-41165056492 / 1000000000000), orderedInterval (49090771661 / 1000000000000) (49090798143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1689892518206277 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29336607874 / 1000000000000) (29336640515 / 1000000000000), orderedInterval (-25456193455 / 1000000000000) (-25456160814 / 1000000000000)))) (orderedInterval (-12708857981 / 1000000000000) (-12708843675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1244767180373101 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37029088875 / 1000000000000) (-37029088874 / 1000000000000), orderedInterval (-25913432201 / 1000000000000) (-25913432200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2132929779946273 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1835347234 / 1000000000000) (-1835347233 / 1000000000000), orderedInterval (34505632887 / 1000000000000) (34505632889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1571106422161507 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30578560230 / 1000000000000) (-30578560229 / 1000000000000), orderedInterval (-26148292556 / 1000000000000) (-26148292555 / 1000000000000)))) (orderedInterval (-2542347153 / 1000000000000) (-2542346994 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate398_chunkChecks4_1 :
    compactCertificate398.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2410481279744461 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7084185985 / 1000000000000) (7084185986 / 1000000000000), orderedInterval (31715313799 / 1000000000000) (31715313800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1391692015736869 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (373929590 / 1000000000000) (373929592 / 1000000000000), orderedInterval (-42774759406 / 1000000000000) (-42774759404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2469581903786921 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21006178380 / 1000000000000) (21006181284 / 1000000000000), orderedInterval (-24304421416 / 1000000000000) (-24304418512 / 1000000000000)))) (orderedInterval (50029758246 / 1000000000000) (50029771968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2307403760256749 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13452782260 / 1000000000000) (-13452782166 / 1000000000000), orderedInterval (30386571080 / 1000000000000) (30386571174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1646672199720317 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30914014530 / 1000000000000) (-30914014529 / 1000000000000), orderedInterval (-24268070077 / 1000000000000) (-24268070076 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1867150770558843 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18493291373 / 1000000000000) (18493292170 / 1000000000000), orderedInterval (-31985886454 / 1000000000000) (-31985885657 / 1000000000000)))) (orderedInterval (-11754453227 / 1000000000000) (-11754452900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1556635652238667 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (15246140710 / 1000000000000) (15246140711 / 1000000000000), orderedInterval (37442960185 / 1000000000000) (37442960186 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1375334806776007 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35161709269 / 1000000000000) (-35161599591 / 1000000000000), orderedInterval (24854124059 / 1000000000000) (24854233737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (398625633252693 / 800000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15419900898 / 1000000000000) (15419901140 / 1000000000000), orderedInterval (-32262278116 / 1000000000000) (-32262277874 / 1000000000000)))) (orderedInterval (10659223077 / 1000000000000) (10659240012 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate398_chunkChecks4_2 :
    compactCertificate398.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1102619480094671 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-977354390 / 1000000000000) (-977354387 / 1000000000000), orderedInterval (48048935981 / 1000000000000) (48048935984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (934702744452631 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47829998014 / 1000000000000) (47830009384 / 1000000000000), orderedInterval (-20998750995 / 1000000000000) (-20998739624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (584893577838493 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39769713439 / 1000000000000) (39769730370 / 1000000000000), orderedInterval (-52786958890 / 1000000000000) (-52786941959 / 1000000000000)))) (orderedInterval (-1304141995 / 1000000000000) (-1304141521 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (314557711429731 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69541883888 / 1000000000000) (-69541883887 / 1000000000000), orderedInterval (-56648331900 / 1000000000000) (-56648331899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (854085376722193 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34243080225 / 1000000000000) (34243080226 / 1000000000000), orderedInterval (42451458126 / 1000000000000) (42451458127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1166180563909361 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7536741192 / 1000000000000) (-7536741191 / 1000000000000), orderedInterval (-46104389701 / 1000000000000) (-46104389700 / 1000000000000)))) (orderedInterval (524102725 / 1000000000000) (524102757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (493106422161507 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-71825168776 / 1000000000000) (-71825168752 / 1000000000000), orderedInterval (-2002149097 / 1000000000000) (-2002149073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2004450229636547 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24480574122 / 1000000000000) (-24480565546 / 1000000000000), orderedInterval (25930298784 / 1000000000000) (25930307359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1338879859028173 / 4000000000000) 4 (IntervalRat.scale (539 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26233830691 / 1000000000000) (26233837174 / 1000000000000), orderedInterval (-34877875551 / 1000000000000) (-34877869068 / 1000000000000)))) (orderedInterval (12082041550 / 1000000000000) (12082053223 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate398_chunkChecks4 :
    compactCertificate398.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate398.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate398_chunkChecks4_0
    compactCertificate398_chunkChecks4_1 compactCertificate398_chunkChecks4_2

theorem compactCertificate398_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate398.chunkCheck r b = true :=
  compactCertificate398.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate398_chunkChecks0
    · exact compactCertificate398_chunkChecks1
    · exact compactCertificate398_chunkChecks2
    · exact compactCertificate398_chunkChecks3
    · exact compactCertificate398_chunkChecks4)

theorem compactCertificate398_coefficient0 :
    compactCertificate398.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate398_coefficient1 :
    compactCertificate398.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate398_coefficient2 :
    compactCertificate398.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate398_coefficient3 :
    compactCertificate398.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate398_coefficient4 :
    compactCertificate398.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate398_coefficients : ∀ r : Fin 5,
    compactCertificate398.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate398_coefficient0
  · exact compactCertificate398_coefficient1
  · exact compactCertificate398_coefficient2
  · exact compactCertificate398_coefficient3
  · exact compactCertificate398_coefficient4

theorem compactCertificate398_lower : (1 : ℚ) ≤ compactCertificate398.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate398, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate398_proves {t : ℝ} (ht : t ∈ compactCertificate398.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate398.proves compactCertificate398_states compactCertificate398_chunks
    compactCertificate398_coefficients compactCertificate398_lower ht

end Erdos232
