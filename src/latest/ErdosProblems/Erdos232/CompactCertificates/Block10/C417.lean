/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate417 : CompactCertificate where
  left := 288
  right := 289
  center := 577 / 2
  grid := fun i =>
    match i.val with
    | 0 => 92
    | 1 => 68
    | 2 => 109
    | 3 => 20
    | 4 => 53
    | 5 => 144
    | 6 => 106
    | 7 => 182
    | 8 => 134
    | 9 => 205
    | 10 => 119
    | 11 => 210
    | 12 => 197
    | 13 => 140
    | 14 => 159
    | 15 => 133
    | 16 => 117
    | 17 => 170
    | 18 => 94
    | 19 => 80
    | 20 => 50
    | 21 => 27
    | 22 => 73
    | 23 => 99
    | 24 => 42
    | 25 => 171
    | _ => 114
  point := fun i =>
    match i.val with
    | 0 => 577 / 2
    | 1 => 850031176938877 / 4000000000000
    | 2 => 274882617629341 / 800000000000
    | 3 => 248036977422839 / 4000000000000
    | 4 => 666262210644683 / 4000000000000
    | 5 => 1809031508358111 / 4000000000000
    | 6 => 1332524421289943 / 4000000000000
    | 7 => 2283303308031539 / 4000000000000
    | 8 => 1681870882351001 / 4000000000000
    | 9 => 2580422446034423 / 4000000000000
    | 10 => 1489807593840767 / 4000000000000
    | 11 => 2643689718896203 / 4000000000000
    | 12 => 2470077865803607 / 4000000000000
    | 13 => 1762764117325831 / 4000000000000
    | 14 => 1998786631934049 / 4000000000000
    | 15 => 1666379909724881 / 4000000000000
    | 16 => 1472297186474501 / 4000000000000
    | 17 => 426729110179599 / 800000000000
    | 18 => 1180355176279453 / 4000000000000
    | 19 => 1000600155007733 / 4000000000000
    | 20 => 626129117648999 / 4000000000000
    | 21 => 336734321883033 / 4000000000000
    | 22 => 914299188068099 / 4000000000000
    | 23 => 1248397375465123 / 4000000000000
    | 24 => 527870882351001 / 4000000000000
    | 25 => 2145765830241721 / 4000000000000
    | _ => 1433272131093239 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))
    | 1 => (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))
    | 2 => (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000))
    | 3 => (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))
    | 4 => (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))
    | 5 => (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000))
    | 6 => (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))
    | 7 => (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))
    | 8 => (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000))
    | 9 => (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))
    | 10 => (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))
    | 11 => (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000))
    | 12 => (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))
    | 13 => (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))
    | 14 => (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000))
    | 15 => (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))
    | 16 => (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))
    | 17 => (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000))
    | 18 => (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))
    | 19 => (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))
    | 20 => (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000))
    | 21 => (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))
    | 22 => (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))
    | 23 => (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000))
    | 24 => (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))
    | 25 => (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))
    | _ => (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2248576227 / 1000000000000) (2248577125 / 1000000000000)
      | 1 => orderedInterval (-3268326877 / 1000000000000) (-3268326841 / 1000000000000)
      | 2 => orderedInterval (422292411 / 1000000000000) (422292428 / 1000000000000)
      | 3 => orderedInterval (11163953621 / 1000000000000) (11163969563 / 1000000000000)
      | 4 => orderedInterval (3408735043 / 1000000000000) (3408735185 / 1000000000000)
      | 5 => orderedInterval (2596774443 / 1000000000000) (2596774477 / 1000000000000)
      | 6 => orderedInterval (-2390382929 / 1000000000000) (-2390382822 / 1000000000000)
      | 7 => orderedInterval (3570129970 / 1000000000000) (3570130405 / 1000000000000)
      | _ => orderedInterval (-6143613529 / 1000000000000) (-6143613449 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19478485136 / 1000000000000) (19478486203 / 1000000000000)
      | 1 => orderedInterval (-4413914668 / 1000000000000) (-4413914628 / 1000000000000)
      | 2 => orderedInterval (-695708969 / 1000000000000) (-695708940 / 1000000000000)
      | 3 => orderedInterval (-10824321726 / 1000000000000) (-10824285771 / 1000000000000)
      | 4 => orderedInterval (751161066 / 1000000000000) (751161293 / 1000000000000)
      | 5 => orderedInterval (1864203885 / 1000000000000) (1864203933 / 1000000000000)
      | 6 => orderedInterval (-7607996778 / 1000000000000) (-7607996680 / 1000000000000)
      | 7 => orderedInterval (314037997 / 1000000000000) (314038462 / 1000000000000)
      | _ => orderedInterval (-264132950 / 1000000000000) (-264132837 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1412869282 / 1000000000000) (-1412868010 / 1000000000000)
      | 1 => orderedInterval (4562183039 / 1000000000000) (4562183094 / 1000000000000)
      | 2 => orderedInterval (-1186369629 / 1000000000000) (-1186369578 / 1000000000000)
      | 3 => orderedInterval (-50919064715 / 1000000000000) (-50918983200 / 1000000000000)
      | 4 => orderedInterval (-7331510096 / 1000000000000) (-7331509725 / 1000000000000)
      | 5 => orderedInterval (-4522162705 / 1000000000000) (-4522162633 / 1000000000000)
      | 6 => orderedInterval (3215528212 / 1000000000000) (3215528302 / 1000000000000)
      | 7 => orderedInterval (-3913095643 / 1000000000000) (-3913095141 / 1000000000000)
      | _ => orderedInterval (9803739095 / 1000000000000) (9803739261 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19784195291 / 1000000000000) (-19784193778 / 1000000000000)
      | 1 => orderedInterval (8432063321 / 1000000000000) (8432063403 / 1000000000000)
      | 2 => orderedInterval (5086082869 / 1000000000000) (5086082961 / 1000000000000)
      | 3 => orderedInterval (44486607174 / 1000000000000) (44486792089 / 1000000000000)
      | 4 => orderedInterval (-4165720047 / 1000000000000) (-4165719431 / 1000000000000)
      | 5 => orderedInterval (-5655463224 / 1000000000000) (-5655463116 / 1000000000000)
      | 6 => orderedInterval (8096793944 / 1000000000000) (8096794030 / 1000000000000)
      | 7 => orderedInterval (663289643 / 1000000000000) (663290185 / 1000000000000)
      | _ => orderedInterval (-9433613404 / 1000000000000) (-9433613148 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (133965051 / 1000000000000) (133966857 / 1000000000000)
      | 1 => orderedInterval (-10040590634 / 1000000000000) (-10040590507 / 1000000000000)
      | 2 => orderedInterval (3632133962 / 1000000000000) (3632134132 / 1000000000000)
      | 3 => orderedInterval (249976547719 / 1000000000000) (249976968367 / 1000000000000)
      | 4 => orderedInterval (14110053438 / 1000000000000) (14110054489 / 1000000000000)
      | 5 => orderedInterval (8256793888 / 1000000000000) (8256794057 / 1000000000000)
      | 6 => orderedInterval (-3742280454 / 1000000000000) (-3742280373 / 1000000000000)
      | 7 => orderedInterval (4542645504 / 1000000000000) (4542646090 / 1000000000000)
      | _ => orderedInterval (-14875194909 / 1000000000000) (-14875194497 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11608138380 / 1000000000000) (11608156071 / 1000000000000)
    | 1 => orderedInterval (-1398187007 / 1000000000000) (-1398148965 / 1000000000000)
    | 2 => orderedInterval (-51703621724 / 1000000000000) (-51703537630 / 1000000000000)
    | 3 => orderedInterval (27725844985 / 1000000000000) (27726033195 / 1000000000000)
    | _ => orderedInterval (251994073565 / 1000000000000) (251994498615 / 1000000000000)

theorem compactCertificate417_stateChecks0 :
    compactCertificate417.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (577 / 2)) (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (850031176938877 / 4000000000000)) (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (274882617629341 / 800000000000)) (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks1 :
    compactCertificate417.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (248036977422839 / 4000000000000)) (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (666262210644683 / 4000000000000)) (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1809031508358111 / 4000000000000)) (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks2 :
    compactCertificate417.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1332524421289943 / 4000000000000)) (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2283303308031539 / 4000000000000)) (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1681870882351001 / 4000000000000)) (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks3 :
    compactCertificate417.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2580422446034423 / 4000000000000)) (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1489807593840767 / 4000000000000)) (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2643689718896203 / 4000000000000)) (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks4 :
    compactCertificate417.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2470077865803607 / 4000000000000)) (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1762764117325831 / 4000000000000)) (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1998786631934049 / 4000000000000)) (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks5 :
    compactCertificate417.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1666379909724881 / 4000000000000)) (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1472297186474501 / 4000000000000)) (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (426729110179599 / 800000000000)) (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks6 :
    compactCertificate417.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1180355176279453 / 4000000000000)) (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1000600155007733 / 4000000000000)) (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (626129117648999 / 4000000000000)) (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks7 :
    compactCertificate417.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (336734321883033 / 4000000000000)) (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (914299188068099 / 4000000000000)) (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1248397375465123 / 4000000000000)) (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_stateChecks8 :
    compactCertificate417.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (527870882351001 / 4000000000000)) (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2145765830241721 / 4000000000000)) (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1433272131093239 / 4000000000000)) (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_states : ∀ j,
    BesselStateValid (compactCertificate417.point j) (compactCertificate417.state j) :=
  compactCertificate417.statesValid_of_checks3 compactCertificate417_stateChecks0
    compactCertificate417_stateChecks1 compactCertificate417_stateChecks2
    compactCertificate417_stateChecks3 compactCertificate417_stateChecks4
    compactCertificate417_stateChecks5 compactCertificate417_stateChecks6
    compactCertificate417_stateChecks7 compactCertificate417_stateChecks8

theorem compactCertificate417_chunkChecks0_0 :
    compactCertificate417.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (577 / 2) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (850031176938877 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (274882617629341 / 800000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000)))) (orderedInterval (2248576227 / 1000000000000) (2248577125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (248036977422839 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (666262210644683 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1809031508358111 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000)))) (orderedInterval (-3268326877 / 1000000000000) (-3268326841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1332524421289943 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2283303308031539 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1681870882351001 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000)))) (orderedInterval (422292411 / 1000000000000) (422292428 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks0_1 :
    compactCertificate417.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2580422446034423 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1489807593840767 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2643689718896203 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000)))) (orderedInterval (11163953621 / 1000000000000) (11163969563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2470077865803607 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1762764117325831 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1998786631934049 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000)))) (orderedInterval (3408735043 / 1000000000000) (3408735185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1666379909724881 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1472297186474501 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (426729110179599 / 800000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000)))) (orderedInterval (2596774443 / 1000000000000) (2596774477 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks0_2 :
    compactCertificate417.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1180355176279453 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1000600155007733 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (626129117648999 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000)))) (orderedInterval (-2390382929 / 1000000000000) (-2390382822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (336734321883033 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (914299188068099 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1248397375465123 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000)))) (orderedInterval (3570129970 / 1000000000000) (3570130405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (527870882351001 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2145765830241721 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1433272131093239 / 4000000000000) 0 (IntervalRat.scale (577 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000)))) (orderedInterval (-6143613529 / 1000000000000) (-6143613449 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks0 :
    compactCertificate417.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate417.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate417_chunkChecks0_0
    compactCertificate417_chunkChecks0_1 compactCertificate417_chunkChecks0_2

theorem compactCertificate417_chunkChecks1_0 :
    compactCertificate417.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (577 / 2) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (850031176938877 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (274882617629341 / 800000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000)))) (orderedInterval (19478485136 / 1000000000000) (19478486203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (248036977422839 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (666262210644683 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1809031508358111 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000)))) (orderedInterval (-4413914668 / 1000000000000) (-4413914628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1332524421289943 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2283303308031539 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1681870882351001 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000)))) (orderedInterval (-695708969 / 1000000000000) (-695708940 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks1_1 :
    compactCertificate417.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2580422446034423 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1489807593840767 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2643689718896203 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000)))) (orderedInterval (-10824321726 / 1000000000000) (-10824285771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2470077865803607 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1762764117325831 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1998786631934049 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000)))) (orderedInterval (751161066 / 1000000000000) (751161293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1666379909724881 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1472297186474501 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (426729110179599 / 800000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000)))) (orderedInterval (1864203885 / 1000000000000) (1864203933 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks1_2 :
    compactCertificate417.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1180355176279453 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1000600155007733 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (626129117648999 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000)))) (orderedInterval (-7607996778 / 1000000000000) (-7607996680 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (336734321883033 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (914299188068099 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1248397375465123 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000)))) (orderedInterval (314037997 / 1000000000000) (314038462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (527870882351001 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2145765830241721 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1433272131093239 / 4000000000000) 1 (IntervalRat.scale (577 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000)))) (orderedInterval (-264132950 / 1000000000000) (-264132837 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks1 :
    compactCertificate417.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate417.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate417_chunkChecks1_0
    compactCertificate417_chunkChecks1_1 compactCertificate417_chunkChecks1_2

theorem compactCertificate417_chunkChecks2_0 :
    compactCertificate417.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (577 / 2) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (850031176938877 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (274882617629341 / 800000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000)))) (orderedInterval (-1412869282 / 1000000000000) (-1412868010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (248036977422839 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (666262210644683 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1809031508358111 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000)))) (orderedInterval (4562183039 / 1000000000000) (4562183094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1332524421289943 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2283303308031539 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1681870882351001 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000)))) (orderedInterval (-1186369629 / 1000000000000) (-1186369578 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks2_1 :
    compactCertificate417.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2580422446034423 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1489807593840767 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2643689718896203 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000)))) (orderedInterval (-50919064715 / 1000000000000) (-50918983200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2470077865803607 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1762764117325831 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1998786631934049 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000)))) (orderedInterval (-7331510096 / 1000000000000) (-7331509725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1666379909724881 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1472297186474501 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (426729110179599 / 800000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000)))) (orderedInterval (-4522162705 / 1000000000000) (-4522162633 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks2_2 :
    compactCertificate417.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1180355176279453 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1000600155007733 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (626129117648999 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000)))) (orderedInterval (3215528212 / 1000000000000) (3215528302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (336734321883033 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (914299188068099 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1248397375465123 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000)))) (orderedInterval (-3913095643 / 1000000000000) (-3913095141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (527870882351001 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2145765830241721 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1433272131093239 / 4000000000000) 2 (IntervalRat.scale (577 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000)))) (orderedInterval (9803739095 / 1000000000000) (9803739261 / 1000000000000))) = true
  rfl'

theorem compactCertificate417_chunkChecks2 :
    compactCertificate417.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate417.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate417_chunkChecks2_0
    compactCertificate417_chunkChecks2_1 compactCertificate417_chunkChecks2_2

theorem compactCertificate417_chunkChecks3_0 :
    compactCertificate417.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (577 / 2) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (850031176938877 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (274882617629341 / 800000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000)))) (orderedInterval (-19784195291 / 1000000000000) (-19784193778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (248036977422839 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (666262210644683 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1809031508358111 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000)))) (orderedInterval (8432063321 / 1000000000000) (8432063403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1332524421289943 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2283303308031539 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1681870882351001 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000)))) (orderedInterval (5086082869 / 1000000000000) (5086082961 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate417_chunkChecks3_1 :
    compactCertificate417.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2580422446034423 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1489807593840767 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2643689718896203 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000)))) (orderedInterval (44486607174 / 1000000000000) (44486792089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2470077865803607 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1762764117325831 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1998786631934049 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000)))) (orderedInterval (-4165720047 / 1000000000000) (-4165719431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1666379909724881 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1472297186474501 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (426729110179599 / 800000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000)))) (orderedInterval (-5655463224 / 1000000000000) (-5655463116 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate417_chunkChecks3_2 :
    compactCertificate417.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1180355176279453 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1000600155007733 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (626129117648999 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000)))) (orderedInterval (8096793944 / 1000000000000) (8096794030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (336734321883033 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (914299188068099 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1248397375465123 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000)))) (orderedInterval (663289643 / 1000000000000) (663290185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (527870882351001 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2145765830241721 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1433272131093239 / 4000000000000) 3 (IntervalRat.scale (577 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000)))) (orderedInterval (-9433613404 / 1000000000000) (-9433613148 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate417_chunkChecks3 :
    compactCertificate417.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate417.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate417_chunkChecks3_0
    compactCertificate417_chunkChecks3_1 compactCertificate417_chunkChecks3_2

theorem compactCertificate417_chunkChecks4_0 :
    compactCertificate417.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (577 / 2) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12005561810 / 1000000000000) (12005561811 / 1000000000000), orderedInterval (45394209328 / 1000000000000) (45394209329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (850031176938877 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18030623622 / 1000000000000) (-18030623245 / 1000000000000), orderedInterval (51720764533 / 1000000000000) (51720764910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (274882617629341 / 800000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39910570118 / 1000000000000) (-39910555228 / 1000000000000), orderedInterval (16180140476 / 1000000000000) (16180155366 / 1000000000000)))) (orderedInterval (133965051 / 1000000000000) (133966857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (248036977422839 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-3973458033 / 1000000000000) (-3973458017 / 1000000000000), orderedInterval (101279626250 / 1000000000000) (101279626266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (666262210644683 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46273827602 / 1000000000000) (-46273827601 / 1000000000000), orderedInterval (-40858268665 / 1000000000000) (-40858268664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1809031508358111 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22814826445 / 1000000000000) (22814826446 / 1000000000000), orderedInterval (29759532018 / 1000000000000) (29759532019 / 1000000000000)))) (orderedInterval (-10040590634 / 1000000000000) (-10040590507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1332524421289943 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34440915546 / 1000000000000) (34440915547 / 1000000000000), orderedInterval (26871188325 / 1000000000000) (26871188326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2283303308031539 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5282819055 / 1000000000000) (-5282819052 / 1000000000000), orderedInterval (32979666558 / 1000000000000) (32979666560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1681870882351001 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10731084660 / 1000000000000) (10731084661 / 1000000000000), orderedInterval (37389377934 / 1000000000000) (37389377935 / 1000000000000)))) (orderedInterval (3632133962 / 1000000000000) (3632134132 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate417_chunkChecks4_1 :
    compactCertificate417.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2580422446034423 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30070522371 / 1000000000000) (-30070495516 / 1000000000000), orderedInterval (9112299419 / 1000000000000) (9112326273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1489807593840767 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23771043234 / 1000000000000) (23771046985 / 1000000000000), orderedInterval (-33858013064 / 1000000000000) (-33858009313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2643689718896203 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28557036558 / 1000000000000) (28557112370 / 1000000000000), orderedInterval (-12175753036 / 1000000000000) (-12175677223 / 1000000000000)))) (orderedInterval (249976547719 / 1000000000000) (249976968367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2470077865803607 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17839426315 / 1000000000000) (17839427006 / 1000000000000), orderedInterval (-26710618260 / 1000000000000) (-26710617570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1762764117325831 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37878922933 / 1000000000000) (37878923931 / 1000000000000), orderedInterval (-3170371330 / 1000000000000) (-3170370333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1998786631934049 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29414093746 / 1000000000000) (-29414093745 / 1000000000000), orderedInterval (-20189948101 / 1000000000000) (-20189948100 / 1000000000000)))) (orderedInterval (14110053438 / 1000000000000) (14110054489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1666379909724881 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17064958364 / 1000000000000) (17064958807 / 1000000000000), orderedInterval (-35190614555 / 1000000000000) (-35190614111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1472297186474501 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994146996 / 1000000000000) (-39994146992 / 1000000000000), orderedInterval (-11350174288 / 1000000000000) (-11350174284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (426729110179599 / 800000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4334558459 / 1000000000000) (4334558460 / 1000000000000), orderedInterval (34269826643 / 1000000000000) (34269826644 / 1000000000000)))) (orderedInterval (8256793888 / 1000000000000) (8256794057 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate417_chunkChecks4_2 :
    compactCertificate417.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1180355176279453 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24831868225 / 1000000000000) (24831868226 / 1000000000000), orderedInterval (39210484126 / 1000000000000) (39210484127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1000600155007733 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19294967845 / 1000000000000) (-19294967238 / 1000000000000), orderedInterval (46650362548 / 1000000000000) (46650363155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (626129117648999 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (14988382702 / 1000000000000) (14988382703 / 1000000000000), orderedInterval (61939106281 / 1000000000000) (61939106282 / 1000000000000)))) (orderedInterval (-3742280454 / 1000000000000) (-3742280373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (336734321883033 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-12521455786 / 1000000000000) (-12521455785 / 1000000000000), orderedInterval (-85981547997 / 1000000000000) (-85981547996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (914299188068099 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1234001995 / 1000000000000) (-1234001993 / 1000000000000), orderedInterval (-52757648989 / 1000000000000) (-52757648987 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1248397375465123 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43201636569 / 1000000000000) (-43201631341 / 1000000000000), orderedInterval (13237926717 / 1000000000000) (13237931945 / 1000000000000)))) (orderedInterval (4542645504 / 1000000000000) (4542646090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (527870882351001 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50078905954 / 1000000000000) (50078905955 / 1000000000000), orderedInterval (47936748361 / 1000000000000) (47936748362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2145765830241721 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-491881075 / 1000000000000) (-491881074 / 1000000000000), orderedInterval (-34445217642 / 1000000000000) (-34445217641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1433272131093239 / 4000000000000) 4 (IntervalRat.scale (577 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34566250610 / 1000000000000) (34566250611 / 1000000000000), orderedInterval (24073600636 / 1000000000000) (24073600637 / 1000000000000)))) (orderedInterval (-14875194909 / 1000000000000) (-14875194497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate417_chunkChecks4 :
    compactCertificate417.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate417.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate417_chunkChecks4_0
    compactCertificate417_chunkChecks4_1 compactCertificate417_chunkChecks4_2

theorem compactCertificate417_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate417.chunkCheck r b = true :=
  compactCertificate417.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate417_chunkChecks0
    · exact compactCertificate417_chunkChecks1
    · exact compactCertificate417_chunkChecks2
    · exact compactCertificate417_chunkChecks3
    · exact compactCertificate417_chunkChecks4)

theorem compactCertificate417_coefficient0 :
    compactCertificate417.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate417_coefficient1 :
    compactCertificate417.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate417_coefficient2 :
    compactCertificate417.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate417_coefficient3 :
    compactCertificate417.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate417_coefficient4 :
    compactCertificate417.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate417_coefficients : ∀ r : Fin 5,
    compactCertificate417.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate417_coefficient0
  · exact compactCertificate417_coefficient1
  · exact compactCertificate417_coefficient2
  · exact compactCertificate417_coefficient3
  · exact compactCertificate417_coefficient4

theorem compactCertificate417_lower : (1 : ℚ) ≤ compactCertificate417.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate417, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate417_proves {t : ℝ} (ht : t ∈ compactCertificate417.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate417.proves compactCertificate417_states compactCertificate417_chunks
    compactCertificate417_coefficients compactCertificate417_lower ht

end Erdos232
