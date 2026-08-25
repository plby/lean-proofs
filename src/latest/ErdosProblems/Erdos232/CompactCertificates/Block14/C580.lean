/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate580 : CompactCertificate where
  left := 451
  right := 452
  center := 903 / 2
  grid := fun i =>
    match i.val with
    | 0 => 144
    | 1 => 106
    | 2 => 171
    | 3 => 31
    | 4 => 83
    | 5 => 225
    | 6 => 166
    | 7 => 285
    | 8 => 210
    | 9 => 322
    | 10 => 186
    | 11 => 329
    | 12 => 308
    | 13 => 220
    | 14 => 249
    | 15 => 208
    | 16 => 183
    | 17 => 266
    | 18 => 147
    | 19 => 125
    | 20 => 78
    | 21 => 42
    | 22 => 114
    | 23 => 156
    | 24 => 66
    | 25 => 267
    | _ => 179
  point := fun i =>
    match i.val with
    | 0 => 903 / 2
    | 1 => 1330291425954603 / 4000000000000
    | 2 => 430188914591499 / 800000000000
    | 3 => 388175720299521 / 4000000000000
    | 4 => 1042694586156237 / 4000000000000
    | 5 => 2831118634397529 / 4000000000000
    | 6 => 2085389172313377 / 4000000000000
    | 7 => 3573349891078821 / 4000000000000
    | 8 => 2632113356608239 / 4000000000000
    | 9 => 4038338767364097 / 4000000000000
    | 10 => 2331535974416313 / 4000000000000
    | 11 => 4137351501149517 / 4000000000000
    | 12 => 3865650455495073 / 4000000000000
    | 13 => 2758710568362609 / 4000000000000
    | 14 => 3128083758468711 / 4000000000000
    | 15 => 2607870118685559 / 4000000000000
    | 16 => 2304132338624739 / 4000000000000
    | 17 => 667827359605161 / 800000000000
    | 18 => 1847245622496267 / 4000000000000
    | 19 => 1565930571875187 / 4000000000000
    | 20 => 979886643391761 / 4000000000000
    | 21 => 526986295771887 / 4000000000000
    | 22 => 1430870306456661 / 4000000000000
    | 23 => 1953731074601397 / 4000000000000
    | 24 => 826113356608239 / 4000000000000
    | 25 => 3358104930170319 / 4000000000000
    | _ => 2243058465125121 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))
    | 1 => (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))
    | 2 => (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000))
    | 3 => (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))
    | 4 => (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
    | 5 => (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000))
    | 6 => (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))
    | 7 => (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))
    | 8 => (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000))
    | 9 => (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))
    | 10 => (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))
    | 11 => (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000))
    | 12 => (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))
    | 13 => (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))
    | 14 => (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000))
    | 15 => (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))
    | 16 => (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))
    | 17 => (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000))
    | 18 => (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))
    | 19 => (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))
    | 20 => (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000))
    | 21 => (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))
    | 22 => (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))
    | 23 => (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000))
    | 24 => (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))
    | 25 => (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))
    | _ => (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3359202525 / 1000000000000) (-3359202491 / 1000000000000)
      | 1 => orderedInterval (1314487863 / 1000000000000) (1314488481 / 1000000000000)
      | 2 => orderedInterval (-1374843527 / 1000000000000) (-1374839750 / 1000000000000)
      | 3 => orderedInterval (-845264761 / 1000000000000) (-845252656 / 1000000000000)
      | 4 => orderedInterval (-1562044522 / 1000000000000) (-1562044331 / 1000000000000)
      | 5 => orderedInterval (1497499380 / 1000000000000) (1497501093 / 1000000000000)
      | 6 => orderedInterval (4315636465 / 1000000000000) (4315636601 / 1000000000000)
      | 7 => orderedInterval (1069793282 / 1000000000000) (1069795425 / 1000000000000)
      | _ => orderedInterval (-2288014207 / 1000000000000) (-2288012185 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14466238848 / 1000000000000) (14466238886 / 1000000000000)
      | 1 => orderedInterval (-1075219334 / 1000000000000) (-1075218389 / 1000000000000)
      | 2 => orderedInterval (1207170800 / 1000000000000) (1207178019 / 1000000000000)
      | 3 => orderedInterval (-1172780360 / 1000000000000) (-1172753407 / 1000000000000)
      | 4 => orderedInterval (2698052566 / 1000000000000) (2698052862 / 1000000000000)
      | 5 => orderedInterval (898559389 / 1000000000000) (898561587 / 1000000000000)
      | 6 => orderedInterval (6780942390 / 1000000000000) (6780942515 / 1000000000000)
      | 7 => orderedInterval (-2951856559 / 1000000000000) (-2951854250 / 1000000000000)
      | _ => orderedInterval (5921247667 / 1000000000000) (5921250294 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (4207088080 / 1000000000000) (4207088124 / 1000000000000)
      | 1 => orderedInterval (-4815633651 / 1000000000000) (-4815632179 / 1000000000000)
      | 2 => orderedInterval (4307875970 / 1000000000000) (4307889902 / 1000000000000)
      | 3 => orderedInterval (54071561 / 1000000000000) (54131802 / 1000000000000)
      | 4 => orderedInterval (3170747388 / 1000000000000) (3170747852 / 1000000000000)
      | 5 => orderedInterval (-2214254972 / 1000000000000) (-2214252145 / 1000000000000)
      | 6 => orderedInterval (-3995469140 / 1000000000000) (-3995469022 / 1000000000000)
      | 7 => orderedInterval (-2197011074 / 1000000000000) (-2197008576 / 1000000000000)
      | _ => orderedInterval (-781343225 / 1000000000000) (-781339739 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14086892350 / 1000000000000) (-14086892299 / 1000000000000)
      | 1 => orderedInterval (1383684063 / 1000000000000) (1383686364 / 1000000000000)
      | 2 => orderedInterval (-3547118260 / 1000000000000) (-3547091229 / 1000000000000)
      | 3 => orderedInterval (14210126187 / 1000000000000) (14210260926 / 1000000000000)
      | 4 => orderedInterval (-4401575735 / 1000000000000) (-4401575003 / 1000000000000)
      | 5 => orderedInterval (-3971158245 / 1000000000000) (-3971154606 / 1000000000000)
      | 6 => orderedInterval (-6044318358 / 1000000000000) (-6044318246 / 1000000000000)
      | 7 => orderedInterval (2736496752 / 1000000000000) (2736499453 / 1000000000000)
      | _ => orderedInterval (-9438269199 / 1000000000000) (-9438264461 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-5368998847 / 1000000000000) (-5368998788 / 1000000000000)
      | 1 => orderedInterval (12621418742 / 1000000000000) (12621422350 / 1000000000000)
      | 2 => orderedInterval (-14583000384 / 1000000000000) (-14582947623 / 1000000000000)
      | 3 => orderedInterval (3504049956 / 1000000000000) (3504351919 / 1000000000000)
      | 4 => orderedInterval (-5327995432 / 1000000000000) (-5327994261 / 1000000000000)
      | 5 => orderedInterval (2990055688 / 1000000000000) (2990060395 / 1000000000000)
      | 6 => orderedInterval (4162233112 / 1000000000000) (4162233220 / 1000000000000)
      | 7 => orderedInterval (2747214651 / 1000000000000) (2747217577 / 1000000000000)
      | _ => orderedInterval (16039320241 / 1000000000000) (16039326894 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-1231952552 / 1000000000000) (-1231929813 / 1000000000000)
    | 1 => orderedInterval (26772355407 / 1000000000000) (26772398117 / 1000000000000)
    | 2 => orderedInterval (-2263929063 / 1000000000000) (-2263843981 / 1000000000000)
    | 3 => orderedInterval (-23159025145 / 1000000000000) (-23158849101 / 1000000000000)
    | _ => orderedInterval (16784297727 / 1000000000000) (16784671683 / 1000000000000)

theorem compactCertificate580_stateChecks0 :
    compactCertificate580.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (903 / 2)) (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1330291425954603 / 4000000000000)) (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (430188914591499 / 800000000000)) (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks1 :
    compactCertificate580.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (388175720299521 / 4000000000000)) (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1042694586156237 / 4000000000000)) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2831118634397529 / 4000000000000)) (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks2 :
    compactCertificate580.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2085389172313377 / 4000000000000)) (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (3573349891078821 / 4000000000000)) (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2632113356608239 / 4000000000000)) (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks3 :
    compactCertificate580.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 322 12 (4038338767364097 / 4000000000000)) (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2331535974416313 / 4000000000000)) (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 329 12 (4137351501149517 / 4000000000000)) (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks4 :
    compactCertificate580.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (3865650455495073 / 4000000000000)) (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2758710568362609 / 4000000000000)) (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3128083758468711 / 4000000000000)) (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks5 :
    compactCertificate580.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2607870118685559 / 4000000000000)) (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2304132338624739 / 4000000000000)) (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (667827359605161 / 800000000000)) (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks6 :
    compactCertificate580.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1847245622496267 / 4000000000000)) (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1565930571875187 / 4000000000000)) (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (979886643391761 / 4000000000000)) (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks7 :
    compactCertificate580.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (526986295771887 / 4000000000000)) (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1430870306456661 / 4000000000000)) (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1953731074601397 / 4000000000000)) (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_stateChecks8 :
    compactCertificate580.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (826113356608239 / 4000000000000)) (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3358104930170319 / 4000000000000)) (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2243058465125121 / 4000000000000)) (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_states : ∀ j,
    BesselStateValid (compactCertificate580.point j) (compactCertificate580.state j) :=
  compactCertificate580.statesValid_of_checks3 compactCertificate580_stateChecks0
    compactCertificate580_stateChecks1 compactCertificate580_stateChecks2
    compactCertificate580_stateChecks3 compactCertificate580_stateChecks4
    compactCertificate580_stateChecks5 compactCertificate580_stateChecks6
    compactCertificate580_stateChecks7 compactCertificate580_stateChecks8

theorem compactCertificate580_chunkChecks0_0 :
    compactCertificate580.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (903 / 2) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1330291425954603 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (430188914591499 / 800000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000)))) (orderedInterval (-3359202525 / 1000000000000) (-3359202491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (388175720299521 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2831118634397529 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000)))) (orderedInterval (1314487863 / 1000000000000) (1314488481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2085389172313377 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3573349891078821 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2632113356608239 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000)))) (orderedInterval (-1374843527 / 1000000000000) (-1374839750 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks0_1 :
    compactCertificate580.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4038338767364097 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2331535974416313 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4137351501149517 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000)))) (orderedInterval (-845264761 / 1000000000000) (-845252656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3865650455495073 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2758710568362609 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3128083758468711 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000)))) (orderedInterval (-1562044522 / 1000000000000) (-1562044331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2607870118685559 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2304132338624739 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (667827359605161 / 800000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000)))) (orderedInterval (1497499380 / 1000000000000) (1497501093 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks0_2 :
    compactCertificate580.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1847245622496267 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1565930571875187 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (979886643391761 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000)))) (orderedInterval (4315636465 / 1000000000000) (4315636601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (526986295771887 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1430870306456661 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1953731074601397 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000)))) (orderedInterval (1069793282 / 1000000000000) (1069795425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (826113356608239 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3358104930170319 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2243058465125121 / 4000000000000) 0 (IntervalRat.scale (903 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000)))) (orderedInterval (-2288014207 / 1000000000000) (-2288012185 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks0 :
    compactCertificate580.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate580.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate580_chunkChecks0_0
    compactCertificate580_chunkChecks0_1 compactCertificate580_chunkChecks0_2

theorem compactCertificate580_chunkChecks1_0 :
    compactCertificate580.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (903 / 2) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1330291425954603 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (430188914591499 / 800000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000)))) (orderedInterval (14466238848 / 1000000000000) (14466238886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (388175720299521 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2831118634397529 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000)))) (orderedInterval (-1075219334 / 1000000000000) (-1075218389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2085389172313377 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3573349891078821 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2632113356608239 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000)))) (orderedInterval (1207170800 / 1000000000000) (1207178019 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks1_1 :
    compactCertificate580.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4038338767364097 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2331535974416313 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4137351501149517 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000)))) (orderedInterval (-1172780360 / 1000000000000) (-1172753407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3865650455495073 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2758710568362609 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3128083758468711 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000)))) (orderedInterval (2698052566 / 1000000000000) (2698052862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2607870118685559 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2304132338624739 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (667827359605161 / 800000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000)))) (orderedInterval (898559389 / 1000000000000) (898561587 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks1_2 :
    compactCertificate580.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1847245622496267 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1565930571875187 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (979886643391761 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000)))) (orderedInterval (6780942390 / 1000000000000) (6780942515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (526986295771887 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1430870306456661 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1953731074601397 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000)))) (orderedInterval (-2951856559 / 1000000000000) (-2951854250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (826113356608239 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3358104930170319 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2243058465125121 / 4000000000000) 1 (IntervalRat.scale (903 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000)))) (orderedInterval (5921247667 / 1000000000000) (5921250294 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks1 :
    compactCertificate580.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate580.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate580_chunkChecks1_0
    compactCertificate580_chunkChecks1_1 compactCertificate580_chunkChecks1_2

theorem compactCertificate580_chunkChecks2_0 :
    compactCertificate580.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (903 / 2) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1330291425954603 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (430188914591499 / 800000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000)))) (orderedInterval (4207088080 / 1000000000000) (4207088124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (388175720299521 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2831118634397529 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000)))) (orderedInterval (-4815633651 / 1000000000000) (-4815632179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2085389172313377 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3573349891078821 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2632113356608239 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000)))) (orderedInterval (4307875970 / 1000000000000) (4307889902 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks2_1 :
    compactCertificate580.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4038338767364097 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2331535974416313 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4137351501149517 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000)))) (orderedInterval (54071561 / 1000000000000) (54131802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3865650455495073 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2758710568362609 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3128083758468711 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000)))) (orderedInterval (3170747388 / 1000000000000) (3170747852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2607870118685559 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2304132338624739 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (667827359605161 / 800000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000)))) (orderedInterval (-2214254972 / 1000000000000) (-2214252145 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks2_2 :
    compactCertificate580.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1847245622496267 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1565930571875187 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (979886643391761 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000)))) (orderedInterval (-3995469140 / 1000000000000) (-3995469022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (526986295771887 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1430870306456661 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1953731074601397 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000)))) (orderedInterval (-2197011074 / 1000000000000) (-2197008576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (826113356608239 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3358104930170319 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2243058465125121 / 4000000000000) 2 (IntervalRat.scale (903 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000)))) (orderedInterval (-781343225 / 1000000000000) (-781339739 / 1000000000000))) = true
  rfl'

theorem compactCertificate580_chunkChecks2 :
    compactCertificate580.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate580.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate580_chunkChecks2_0
    compactCertificate580_chunkChecks2_1 compactCertificate580_chunkChecks2_2

theorem compactCertificate580_chunkChecks3_0 :
    compactCertificate580.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (903 / 2) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1330291425954603 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (430188914591499 / 800000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000)))) (orderedInterval (-14086892350 / 1000000000000) (-14086892299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (388175720299521 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2831118634397529 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000)))) (orderedInterval (1383684063 / 1000000000000) (1383686364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2085389172313377 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3573349891078821 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2632113356608239 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000)))) (orderedInterval (-3547118260 / 1000000000000) (-3547091229 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate580_chunkChecks3_1 :
    compactCertificate580.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4038338767364097 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2331535974416313 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4137351501149517 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000)))) (orderedInterval (14210126187 / 1000000000000) (14210260926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3865650455495073 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2758710568362609 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3128083758468711 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000)))) (orderedInterval (-4401575735 / 1000000000000) (-4401575003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2607870118685559 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2304132338624739 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (667827359605161 / 800000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000)))) (orderedInterval (-3971158245 / 1000000000000) (-3971154606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate580_chunkChecks3_2 :
    compactCertificate580.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1847245622496267 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1565930571875187 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (979886643391761 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000)))) (orderedInterval (-6044318358 / 1000000000000) (-6044318246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (526986295771887 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1430870306456661 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1953731074601397 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000)))) (orderedInterval (2736496752 / 1000000000000) (2736499453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (826113356608239 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3358104930170319 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2243058465125121 / 4000000000000) 3 (IntervalRat.scale (903 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000)))) (orderedInterval (-9438269199 / 1000000000000) (-9438264461 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate580_chunkChecks3 :
    compactCertificate580.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate580.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate580_chunkChecks3_0
    compactCertificate580_chunkChecks3_1 compactCertificate580_chunkChecks3_2

theorem compactCertificate580_chunkChecks4_0 :
    compactCertificate580.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (903 / 2) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3906420452 / 1000000000000) (-3906420449 / 1000000000000), orderedInterval (37350695277 / 1000000000000) (37350695280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1330291425954603 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14963671149 / 1000000000000) (14963671150 / 1000000000000), orderedInterval (41090964455 / 1000000000000) (41090964456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (430188914591499 / 800000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33234981107 / 1000000000000) (-33234981089 / 1000000000000), orderedInterval (-8875518730 / 1000000000000) (-8875518712 / 1000000000000)))) (orderedInterval (-5368998847 / 1000000000000) (-5368998788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (388175720299521 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34400911553 / 1000000000000) (-34400911552 / 1000000000000), orderedInterval (-73149102302 / 1000000000000) (-73149102301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2831118634397529 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29715145153 / 1000000000000) (-29715137228 / 1000000000000), orderedInterval (4079381323 / 1000000000000) (4079389248 / 1000000000000)))) (orderedInterval (12621418742 / 1000000000000) (12621422350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2085389172313377 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20532747853 / 1000000000000) (20532747854 / 1000000000000), orderedInterval (28255940854 / 1000000000000) (28255940855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3573349891078821 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25170287771 / 1000000000000) (25170394066 / 1000000000000), orderedInterval (-8907090288 / 1000000000000) (-8906983993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2632113356608239 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24763620724 / 1000000000000) (-24763601181 / 1000000000000), orderedInterval (18839780819 / 1000000000000) (18839800361 / 1000000000000)))) (orderedInterval (-14583000384 / 1000000000000) (-14582947623 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate580_chunkChecks4_1 :
    compactCertificate580.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4038338767364097 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23606659921 / 1000000000000) (-23606599906 / 1000000000000), orderedInterval (8573368113 / 1000000000000) (8573428128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2331535974416313 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20446178841 / 1000000000000) (-20446176726 / 1000000000000), orderedInterval (25981809289 / 1000000000000) (25981811405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4137351501149517 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24796572264 / 1000000000000) (-24796564481 / 1000000000000), orderedInterval (-772513967 / 1000000000000) (-772506184 / 1000000000000)))) (orderedInterval (3504049956 / 1000000000000) (3504351919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3865650455495073 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10293170331 / 1000000000000) (-10293170326 / 1000000000000), orderedInterval (23516939807 / 1000000000000) (23516939811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2758710568362609 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19281240198 / 1000000000000) (-19281238757 / 1000000000000), orderedInterval (23493808329 / 1000000000000) (23493809770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3128083758468711 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14903708502 / 1000000000000) (-14903708501 / 1000000000000), orderedInterval (-24320483995 / 1000000000000) (-24320483994 / 1000000000000)))) (orderedInterval (-5327995432 / 1000000000000) (-5327994261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2607870118685559 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20095722136 / 1000000000000) (-20095720103 / 1000000000000), orderedInterval (23944918781 / 1000000000000) (23944920814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2304132338624739 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31385109060 / 1000000000000) (-31385080289 / 1000000000000), orderedInterval (10988735974 / 1000000000000) (10988764745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (667827359605161 / 800000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2597477462 / 1000000000000) (-2597477461 / 1000000000000), orderedInterval (27494631770 / 1000000000000) (27494631771 / 1000000000000)))) (orderedInterval (2990055688 / 1000000000000) (2990060395 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate580_chunkChecks4_2 :
    compactCertificate580.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1847245622496267 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26175338546 / 1000000000000) (-26175338545 / 1000000000000), orderedInterval (-26303755895 / 1000000000000) (-26303755894 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1565930571875187 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16860503074 / 1000000000000) (16860503477 / 1000000000000), orderedInterval (-36653494849 / 1000000000000) (-36653494446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (979886643391761 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33318766602 / 1000000000000) (33318766603 / 1000000000000), orderedInterval (38514493922 / 1000000000000) (38514493923 / 1000000000000)))) (orderedInterval (4162233112 / 1000000000000) (4162233220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (526986295771887 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38334958291 / 1000000000000) (38334958292 / 1000000000000), orderedInterval (57842434837 / 1000000000000) (57842434838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1430870306456661 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14903041572 / 1000000000000) (14903041573 / 1000000000000), orderedInterval (39445257858 / 1000000000000) (39445257859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1953731074601397 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27606854529 / 1000000000000) (-27606827270 / 1000000000000), orderedInterval (23293135184 / 1000000000000) (23293162443 / 1000000000000)))) (orderedInterval (2747214651 / 1000000000000) (2747217577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (826113356608239 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1775397238 / 1000000000000) (-1775397234 / 1000000000000), orderedInterval (55496085122 / 1000000000000) (55496085127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3358104930170319 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27480042511 / 1000000000000) (-27480040616 / 1000000000000), orderedInterval (-1760022772 / 1000000000000) (-1760020878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2243058465125121 / 4000000000000) 4 (IntervalRat.scale (903 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24059678207 / 1000000000000) (24059687496 / 1000000000000), orderedInterval (-23609644518 / 1000000000000) (-23609635229 / 1000000000000)))) (orderedInterval (16039320241 / 1000000000000) (16039326894 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate580_chunkChecks4 :
    compactCertificate580.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate580.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate580_chunkChecks4_0
    compactCertificate580_chunkChecks4_1 compactCertificate580_chunkChecks4_2

theorem compactCertificate580_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate580.chunkCheck r b = true :=
  compactCertificate580.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate580_chunkChecks0
    · exact compactCertificate580_chunkChecks1
    · exact compactCertificate580_chunkChecks2
    · exact compactCertificate580_chunkChecks3
    · exact compactCertificate580_chunkChecks4)

theorem compactCertificate580_coefficient0 :
    compactCertificate580.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate580_coefficient1 :
    compactCertificate580.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate580_coefficient2 :
    compactCertificate580.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate580_coefficient3 :
    compactCertificate580.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate580_coefficient4 :
    compactCertificate580.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate580_coefficients : ∀ r : Fin 5,
    compactCertificate580.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate580_coefficient0
  · exact compactCertificate580_coefficient1
  · exact compactCertificate580_coefficient2
  · exact compactCertificate580_coefficient3
  · exact compactCertificate580_coefficient4

theorem compactCertificate580_lower : (1 : ℚ) ≤ compactCertificate580.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate580, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate580_proves {t : ℝ} (ht : t ∈ compactCertificate580.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate580.proves compactCertificate580_states compactCertificate580_chunks
    compactCertificate580_coefficients compactCertificate580_lower ht

end Erdos232
