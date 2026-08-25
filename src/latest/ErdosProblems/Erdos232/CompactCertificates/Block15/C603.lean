/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate603 : CompactCertificate where
  left := 474
  right := 475
  center := 949 / 2
  grid := fun i =>
    match i.val with
    | 0 => 151
    | 1 => 111
    | 2 => 180
    | 3 => 32
    | 4 => 87
    | 5 => 237
    | 6 => 174
    | 7 => 299
    | 8 => 220
    | 9 => 338
    | 10 => 195
    | 11 => 346
    | 12 => 323
    | 13 => 231
    | 14 => 262
    | 15 => 218
    | 16 => 193
    | 17 => 279
    | 18 => 155
    | 19 => 131
    | 20 => 82
    | 21 => 44
    | 22 => 120
    | 23 => 163
    | 24 => 69
    | 25 => 281
    | _ => 188
  point := fun i =>
    match i.val with
    | 0 => 949 / 2
    | 1 => 1398058209558049 / 4000000000000
    | 2 => 452103300052417 / 800000000000
    | 3 => 407949898742243 / 4000000000000
    | 4 => 1095810810921671 / 4000000000000
    | 5 => 2975339517212907 / 4000000000000
    | 6 => 2191621621844291 / 4000000000000
    | 7 => 3755381004024143 / 4000000000000
    | 8 => 2766196650521837 / 4000000000000
    | 9 => 4244057021294051 / 4000000000000
    | 10 => 2450307463699979 / 4000000000000
    | 11 => 4348113593123911 / 4000000000000
    | 12 => 4062571741157059 / 4000000000000
    | 13 => 2899242889674547 / 4000000000000
    | 14 => 3287432432765013 / 4000000000000
    | 15 => 2740718430379397 / 4000000000000
    | 16 => 2421507850891337 / 4000000000000
    | 17 => 701847357990363 / 800000000000
    | 18 => 1941346728404161 / 4000000000000
    | 19 => 1645701121494521 / 4000000000000
    | 20 => 1029803349478163 / 4000000000000
    | 21 => 553831666320621 / 4000000000000
    | 22 => 1503760709664863 / 4000000000000
    | 23 => 2053256688589951 / 4000000000000
    | 24 => 868196650521837 / 4000000000000
    | 25 => 3529171183534477 / 4000000000000
    | _ => 2357322794467043 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))
    | 1 => (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))
    | 2 => (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000))
    | 3 => (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))
    | 4 => (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))
    | 5 => (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000))
    | 6 => (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))
    | 7 => (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))
    | 8 => (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000))
    | 9 => (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))
    | 10 => (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))
    | 11 => (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000))
    | 12 => (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))
    | 13 => (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))
    | 14 => (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000))
    | 15 => (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))
    | 16 => (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))
    | 17 => (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000))
    | 18 => (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))
    | 19 => (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))
    | 20 => (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000))
    | 21 => (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))
    | 22 => (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))
    | 23 => (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000))
    | 24 => (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))
    | 25 => (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))
    | _ => (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-10995261209 / 1000000000000) (-10995261173 / 1000000000000)
      | 1 => orderedInterval (-2281587355 / 1000000000000) (-2281586574 / 1000000000000)
      | 2 => orderedInterval (912094234 / 1000000000000) (912094261 / 1000000000000)
      | 3 => orderedInterval (1146420146 / 1000000000000) (1146420334 / 1000000000000)
      | 4 => orderedInterval (823427470 / 1000000000000) (823428096 / 1000000000000)
      | 5 => orderedInterval (-681503258 / 1000000000000) (-681503064 / 1000000000000)
      | 6 => orderedInterval (-1938328261 / 1000000000000) (-1938325256 / 1000000000000)
      | 7 => orderedInterval (1614981954 / 1000000000000) (1614986566 / 1000000000000)
      | _ => orderedInterval (3316479361 / 1000000000000) (3316479545 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-6822239665 / 1000000000000) (-6822239625 / 1000000000000)
      | 1 => orderedInterval (3217054975 / 1000000000000) (3217055196 / 1000000000000)
      | 2 => orderedInterval (1923024766 / 1000000000000) (1923024813 / 1000000000000)
      | 3 => orderedInterval (-6608382165 / 1000000000000) (-6608381774 / 1000000000000)
      | 4 => orderedInterval (-4592915571 / 1000000000000) (-4592914262 / 1000000000000)
      | 5 => orderedInterval (2592357748 / 1000000000000) (2592358088 / 1000000000000)
      | 6 => orderedInterval (6256320749 / 1000000000000) (6256323812 / 1000000000000)
      | 7 => orderedInterval (-2176147956 / 1000000000000) (-2176142977 / 1000000000000)
      | _ => orderedInterval (-2889032672 / 1000000000000) (-2889032422 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10485934035 / 1000000000000) (10485934080 / 1000000000000)
      | 1 => orderedInterval (284234072 / 1000000000000) (284234196 / 1000000000000)
      | 2 => orderedInterval (-2358653224 / 1000000000000) (-2358653141 / 1000000000000)
      | 3 => orderedInterval (-11779689615 / 1000000000000) (-11779688777 / 1000000000000)
      | 4 => orderedInterval (-2961291009 / 1000000000000) (-2961288249 / 1000000000000)
      | 5 => orderedInterval (2195398902 / 1000000000000) (2195399508 / 1000000000000)
      | 6 => orderedInterval (3129708395 / 1000000000000) (3129711526 / 1000000000000)
      | 7 => orderedInterval (-2904588857 / 1000000000000) (-2904583466 / 1000000000000)
      | _ => orderedInterval (-6689789046 / 1000000000000) (-6689788692 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5909029392 / 1000000000000) (5909029444 / 1000000000000)
      | 1 => orderedInterval (-7951047284 / 1000000000000) (-7951047142 / 1000000000000)
      | 2 => orderedInterval (-6802731210 / 1000000000000) (-6802731059 / 1000000000000)
      | 3 => orderedInterval (24232169378 / 1000000000000) (24232171214 / 1000000000000)
      | 4 => orderedInterval (11137111973 / 1000000000000) (11137117812 / 1000000000000)
      | 5 => orderedInterval (-4375434264 / 1000000000000) (-4375433174 / 1000000000000)
      | 6 => orderedInterval (-5569273705 / 1000000000000) (-5569270508 / 1000000000000)
      | 7 => orderedInterval (1956604761 / 1000000000000) (1956610591 / 1000000000000)
      | _ => orderedInterval (-3083481822 / 1000000000000) (-3083481300 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9912875500 / 1000000000000) (-9912875440 / 1000000000000)
      | 1 => orderedInterval (625100487 / 1000000000000) (625100696 / 1000000000000)
      | 2 => orderedInterval (6663436594 / 1000000000000) (6663436872 / 1000000000000)
      | 3 => orderedInterval (71209694726 / 1000000000000) (71209698803 / 1000000000000)
      | 4 => orderedInterval (11629120092 / 1000000000000) (11629132497 / 1000000000000)
      | 5 => orderedInterval (-7486526583 / 1000000000000) (-7486524606 / 1000000000000)
      | 6 => orderedInterval (-3777080239 / 1000000000000) (-3777076966 / 1000000000000)
      | 7 => orderedInterval (3410880992 / 1000000000000) (3410887309 / 1000000000000)
      | _ => orderedInterval (14568169622 / 1000000000000) (14568170423 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-8083276918 / 1000000000000) (-8083267265 / 1000000000000)
    | 1 => orderedInterval (-9099959791 / 1000000000000) (-9099949151 / 1000000000000)
    | 2 => orderedInterval (-10598736347 / 1000000000000) (-10598723015 / 1000000000000)
    | 3 => orderedInterval (15452947219 / 1000000000000) (15452965878 / 1000000000000)
    | _ => orderedInterval (86929920191 / 1000000000000) (86929949588 / 1000000000000)

theorem compactCertificate603_stateChecks0 :
    compactCertificate603.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (949 / 2)) (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1398058209558049 / 4000000000000)) (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (452103300052417 / 800000000000)) (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks1 :
    compactCertificate603.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (407949898742243 / 4000000000000)) (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1095810810921671 / 4000000000000)) (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2975339517212907 / 4000000000000)) (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks2 :
    compactCertificate603.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2191621621844291 / 4000000000000)) (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 299 12 (3755381004024143 / 4000000000000)) (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2766196650521837 / 4000000000000)) (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks3 :
    compactCertificate603.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 338 12 (4244057021294051 / 4000000000000)) (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2450307463699979 / 4000000000000)) (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 346 12 (4348113593123911 / 4000000000000)) (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks4 :
    compactCertificate603.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 323 12 (4062571741157059 / 4000000000000)) (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2899242889674547 / 4000000000000)) (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3287432432765013 / 4000000000000)) (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks5 :
    compactCertificate603.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2740718430379397 / 4000000000000)) (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2421507850891337 / 4000000000000)) (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (701847357990363 / 800000000000)) (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks6 :
    compactCertificate603.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1941346728404161 / 4000000000000)) (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1645701121494521 / 4000000000000)) (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1029803349478163 / 4000000000000)) (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks7 :
    compactCertificate603.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (553831666320621 / 4000000000000)) (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1503760709664863 / 4000000000000)) (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2053256688589951 / 4000000000000)) (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_stateChecks8 :
    compactCertificate603.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (868196650521837 / 4000000000000)) (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3529171183534477 / 4000000000000)) (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2357322794467043 / 4000000000000)) (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_states : ∀ j,
    BesselStateValid (compactCertificate603.point j) (compactCertificate603.state j) :=
  compactCertificate603.statesValid_of_checks3 compactCertificate603_stateChecks0
    compactCertificate603_stateChecks1 compactCertificate603_stateChecks2
    compactCertificate603_stateChecks3 compactCertificate603_stateChecks4
    compactCertificate603_stateChecks5 compactCertificate603_stateChecks6
    compactCertificate603_stateChecks7 compactCertificate603_stateChecks8

theorem compactCertificate603_chunkChecks0_0 :
    compactCertificate603.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (949 / 2) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1398058209558049 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (452103300052417 / 800000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000)))) (orderedInterval (-10995261209 / 1000000000000) (-10995261173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (407949898742243 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1095810810921671 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2975339517212907 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000)))) (orderedInterval (-2281587355 / 1000000000000) (-2281586574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2191621621844291 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3755381004024143 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2766196650521837 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000)))) (orderedInterval (912094234 / 1000000000000) (912094261 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks0_1 :
    compactCertificate603.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4244057021294051 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2450307463699979 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4348113593123911 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000)))) (orderedInterval (1146420146 / 1000000000000) (1146420334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4062571741157059 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2899242889674547 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3287432432765013 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000)))) (orderedInterval (823427470 / 1000000000000) (823428096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2740718430379397 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2421507850891337 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (701847357990363 / 800000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000)))) (orderedInterval (-681503258 / 1000000000000) (-681503064 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks0_2 :
    compactCertificate603.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1941346728404161 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1645701121494521 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1029803349478163 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000)))) (orderedInterval (-1938328261 / 1000000000000) (-1938325256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (553831666320621 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1503760709664863 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2053256688589951 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000)))) (orderedInterval (1614981954 / 1000000000000) (1614986566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (868196650521837 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3529171183534477 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2357322794467043 / 4000000000000) 0 (IntervalRat.scale (949 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000)))) (orderedInterval (3316479361 / 1000000000000) (3316479545 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks0 :
    compactCertificate603.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate603.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate603_chunkChecks0_0
    compactCertificate603_chunkChecks0_1 compactCertificate603_chunkChecks0_2

theorem compactCertificate603_chunkChecks1_0 :
    compactCertificate603.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (949 / 2) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1398058209558049 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (452103300052417 / 800000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000)))) (orderedInterval (-6822239665 / 1000000000000) (-6822239625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (407949898742243 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1095810810921671 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2975339517212907 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000)))) (orderedInterval (3217054975 / 1000000000000) (3217055196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2191621621844291 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3755381004024143 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2766196650521837 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000)))) (orderedInterval (1923024766 / 1000000000000) (1923024813 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks1_1 :
    compactCertificate603.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4244057021294051 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2450307463699979 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4348113593123911 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000)))) (orderedInterval (-6608382165 / 1000000000000) (-6608381774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4062571741157059 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2899242889674547 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3287432432765013 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000)))) (orderedInterval (-4592915571 / 1000000000000) (-4592914262 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2740718430379397 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2421507850891337 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (701847357990363 / 800000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000)))) (orderedInterval (2592357748 / 1000000000000) (2592358088 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks1_2 :
    compactCertificate603.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1941346728404161 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1645701121494521 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1029803349478163 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000)))) (orderedInterval (6256320749 / 1000000000000) (6256323812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (553831666320621 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1503760709664863 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2053256688589951 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000)))) (orderedInterval (-2176147956 / 1000000000000) (-2176142977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (868196650521837 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3529171183534477 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2357322794467043 / 4000000000000) 1 (IntervalRat.scale (949 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000)))) (orderedInterval (-2889032672 / 1000000000000) (-2889032422 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks1 :
    compactCertificate603.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate603.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate603_chunkChecks1_0
    compactCertificate603_chunkChecks1_1 compactCertificate603_chunkChecks1_2

theorem compactCertificate603_chunkChecks2_0 :
    compactCertificate603.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (949 / 2) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1398058209558049 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (452103300052417 / 800000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000)))) (orderedInterval (10485934035 / 1000000000000) (10485934080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (407949898742243 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1095810810921671 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2975339517212907 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000)))) (orderedInterval (284234072 / 1000000000000) (284234196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2191621621844291 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3755381004024143 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2766196650521837 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000)))) (orderedInterval (-2358653224 / 1000000000000) (-2358653141 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks2_1 :
    compactCertificate603.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4244057021294051 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2450307463699979 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4348113593123911 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000)))) (orderedInterval (-11779689615 / 1000000000000) (-11779688777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4062571741157059 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2899242889674547 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3287432432765013 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000)))) (orderedInterval (-2961291009 / 1000000000000) (-2961288249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2740718430379397 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2421507850891337 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (701847357990363 / 800000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000)))) (orderedInterval (2195398902 / 1000000000000) (2195399508 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks2_2 :
    compactCertificate603.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1941346728404161 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1645701121494521 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1029803349478163 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000)))) (orderedInterval (3129708395 / 1000000000000) (3129711526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (553831666320621 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1503760709664863 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2053256688589951 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000)))) (orderedInterval (-2904588857 / 1000000000000) (-2904583466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (868196650521837 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3529171183534477 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2357322794467043 / 4000000000000) 2 (IntervalRat.scale (949 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000)))) (orderedInterval (-6689789046 / 1000000000000) (-6689788692 / 1000000000000))) = true
  rfl'

theorem compactCertificate603_chunkChecks2 :
    compactCertificate603.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate603.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate603_chunkChecks2_0
    compactCertificate603_chunkChecks2_1 compactCertificate603_chunkChecks2_2

theorem compactCertificate603_chunkChecks3_0 :
    compactCertificate603.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (949 / 2) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1398058209558049 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (452103300052417 / 800000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000)))) (orderedInterval (5909029392 / 1000000000000) (5909029444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (407949898742243 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1095810810921671 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2975339517212907 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000)))) (orderedInterval (-7951047284 / 1000000000000) (-7951047142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2191621621844291 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3755381004024143 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2766196650521837 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000)))) (orderedInterval (-6802731210 / 1000000000000) (-6802731059 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate603_chunkChecks3_1 :
    compactCertificate603.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4244057021294051 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2450307463699979 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4348113593123911 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000)))) (orderedInterval (24232169378 / 1000000000000) (24232171214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4062571741157059 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2899242889674547 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3287432432765013 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000)))) (orderedInterval (11137111973 / 1000000000000) (11137117812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2740718430379397 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2421507850891337 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (701847357990363 / 800000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000)))) (orderedInterval (-4375434264 / 1000000000000) (-4375433174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate603_chunkChecks3_2 :
    compactCertificate603.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1941346728404161 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1645701121494521 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1029803349478163 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000)))) (orderedInterval (-5569273705 / 1000000000000) (-5569270508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (553831666320621 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1503760709664863 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2053256688589951 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000)))) (orderedInterval (1956604761 / 1000000000000) (1956610591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (868196650521837 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3529171183534477 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2357322794467043 / 4000000000000) 3 (IntervalRat.scale (949 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000)))) (orderedInterval (-3083481822 / 1000000000000) (-3083481300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate603_chunkChecks3 :
    compactCertificate603.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate603.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate603_chunkChecks3_0
    compactCertificate603_chunkChecks3_1 compactCertificate603_chunkChecks3_2

theorem compactCertificate603_chunkChecks4_0 :
    compactCertificate603.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (949 / 2) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28797697275 / 1000000000000) (-28797697274 / 1000000000000), orderedInterval (-22604956500 / 1000000000000) (-22604956499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1398058209558049 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-42675230578 / 1000000000000) (-42675230347 / 1000000000000), orderedInterval (573690814 / 1000000000000) (573691045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (452103300052417 / 800000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919093011 / 1000000000000) (13919093012 / 1000000000000), orderedInterval (30528843289 / 1000000000000) (30528843290 / 1000000000000)))) (orderedInterval (-9912875500 / 1000000000000) (-9912875440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (407949898742243 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61932735352 / 1000000000000) (61932802034 / 1000000000000), orderedInterval (-49359250517 / 1000000000000) (-49359183835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1095810810921671 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47652380355 / 1000000000000) (-47652380342 / 1000000000000), orderedInterval (-7198487479 / 1000000000000) (-7198487467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2975339517212907 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1831649047 / 1000000000000) (-1831649046 / 1000000000000), orderedInterval (-29196490225 / 1000000000000) (-29196490224 / 1000000000000)))) (orderedInterval (625100487 / 1000000000000) (625100696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2191621621844291 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30192900776 / 1000000000000) (30192992885 / 1000000000000), orderedInterval (-15848504926 / 1000000000000) (-15848412816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3755381004024143 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7553772898 / 1000000000000) (-7553772897 / 1000000000000), orderedInterval (-24916423994 / 1000000000000) (-24916423993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2766196650521837 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28099342522 / 1000000000000) (28099342531 / 1000000000000), orderedInterval (11425088865 / 1000000000000) (11425088873 / 1000000000000)))) (orderedInterval (6663436594 / 1000000000000) (6663436872 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate603_chunkChecks4_1 :
    compactCertificate603.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4244057021294051 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1439023980 / 1000000000000) (-1439023979 / 1000000000000), orderedInterval (24453486771 / 1000000000000) (24453486772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2450307463699979 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22009427590 / 1000000000000) (-22009427589 / 1000000000000), orderedInterval (-23536948248 / 1000000000000) (-23536948247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4348113593123911 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17737151003 / 1000000000000) (17737151005 / 1000000000000), orderedInterval (16455283776 / 1000000000000) (16455283778 / 1000000000000)))) (orderedInterval (71209694726 / 1000000000000) (71209698803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4062571741157059 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24847170563 / 1000000000000) (-24847139073 / 1000000000000), orderedInterval (3083593637 / 1000000000000) (3083625127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2899242889674547 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3311029328 / 1000000000000) (3311029329 / 1000000000000), orderedInterval (-29453308375 / 1000000000000) (-29453308374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3287432432765013 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12204052940 / 1000000000000) (-12204052914 / 1000000000000), orderedInterval (25020851062 / 1000000000000) (25020851088 / 1000000000000)))) (orderedInterval (11629120092 / 1000000000000) (11629132497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2740718430379397 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27132511783 / 1000000000000) (27132511785 / 1000000000000), orderedInterval (13871023745 / 1000000000000) (13871023748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2421507850891337 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5333743746 / 1000000000000) (5333743748 / 1000000000000), orderedInterval (-31991283369 / 1000000000000) (-31991283367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (701847357990363 / 800000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26932879372 / 1000000000000) (-26932873578 / 1000000000000), orderedInterval (535390836 / 1000000000000) (535396630 / 1000000000000)))) (orderedInterval (-7486526583 / 1000000000000) (-7486524606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate603_chunkChecks4_2 :
    compactCertificate603.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1941346728404161 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26604418492 / 1000000000000) (26604436544 / 1000000000000), orderedInterval (-24602035666 / 1000000000000) (-24602017614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1645701121494521 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24171743377 / 1000000000000) (-24171743376 / 1000000000000), orderedInterval (-31004141851 / 1000000000000) (-31004141850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1029803349478163 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (29101294037 / 1000000000000) (29101294038 / 1000000000000), orderedInterval (40265908329 / 1000000000000) (40265908330 / 1000000000000)))) (orderedInterval (-3777080239 / 1000000000000) (-3777076966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (553831666320621 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57505878032 / 1000000000000) (57505878033 / 1000000000000), orderedInterval (35722694630 / 1000000000000) (35722694631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1503760709664863 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-10812590890 / 1000000000000) (-10812590844 / 1000000000000), orderedInterval (39719497327 / 1000000000000) (39719497373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2053256688589951 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31727184217 / 1000000000000) (-31727124793 / 1000000000000), orderedInterval (15314915491 / 1000000000000) (15314974915 / 1000000000000)))) (orderedInterval (3410880992 / 1000000000000) (3410887309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (868196650521837 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47352729391 / 1000000000000) (-47352729390 / 1000000000000), orderedInterval (-26173650907 / 1000000000000) (-26173650906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3529171183534477 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7694464993 / 1000000000000) (-7694464992 / 1000000000000), orderedInterval (-25731740579 / 1000000000000) (-25731740578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2357322794467043 / 4000000000000) 4 (IntervalRat.scale (949 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15859133503 / 1000000000000) (-15859133223 / 1000000000000), orderedInterval (28801127700 / 1000000000000) (28801127981 / 1000000000000)))) (orderedInterval (14568169622 / 1000000000000) (14568170423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate603_chunkChecks4 :
    compactCertificate603.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate603.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate603_chunkChecks4_0
    compactCertificate603_chunkChecks4_1 compactCertificate603_chunkChecks4_2

theorem compactCertificate603_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate603.chunkCheck r b = true :=
  compactCertificate603.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate603_chunkChecks0
    · exact compactCertificate603_chunkChecks1
    · exact compactCertificate603_chunkChecks2
    · exact compactCertificate603_chunkChecks3
    · exact compactCertificate603_chunkChecks4)

theorem compactCertificate603_coefficient0 :
    compactCertificate603.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate603_coefficient1 :
    compactCertificate603.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate603_coefficient2 :
    compactCertificate603.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate603_coefficient3 :
    compactCertificate603.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate603_coefficient4 :
    compactCertificate603.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate603_coefficients : ∀ r : Fin 5,
    compactCertificate603.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate603_coefficient0
  · exact compactCertificate603_coefficient1
  · exact compactCertificate603_coefficient2
  · exact compactCertificate603_coefficient3
  · exact compactCertificate603_coefficient4

theorem compactCertificate603_lower : (1 : ℚ) ≤ compactCertificate603.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate603, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate603_proves {t : ℝ} (ht : t ∈ compactCertificate603.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate603.proves compactCertificate603_states compactCertificate603_chunks
    compactCertificate603_coefficients compactCertificate603_lower ht

end Erdos232
