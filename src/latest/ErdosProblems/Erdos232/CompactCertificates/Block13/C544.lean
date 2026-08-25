/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate544 : CompactCertificate where
  left := 415
  right := 416
  center := 831 / 2
  grid := fun i =>
    match i.val with
    | 0 => 132
    | 1 => 97
    | 2 => 158
    | 3 => 28
    | 4 => 76
    | 5 => 207
    | 6 => 153
    | 7 => 262
    | 8 => 193
    | 9 => 296
    | 10 => 171
    | 11 => 303
    | 12 => 283
    | 13 => 202
    | 14 => 229
    | 15 => 191
    | 16 => 169
    | 17 => 245
    | 18 => 135
    | 19 => 115
    | 20 => 72
    | 21 => 39
    | 22 => 105
    | 23 => 143
    | 24 => 61
    | 25 => 246
    | _ => 164
  point := fun i =>
    match i.val with
    | 0 => 831 / 2
    | 1 => 1224221677705731 / 4000000000000
    | 2 => 395888137348323 / 800000000000
    | 3 => 357224832302217 / 4000000000000
    | 4 => 959556147392949 / 4000000000000
    | 5 => 2605381600425633 / 4000000000000
    | 6 => 1919112294786729 / 4000000000000
    | 7 => 3288431627338317 / 4000000000000
    | 8 => 2422243853091303 / 4000000000000
    | 9 => 3716344978604169 / 4000000000000
    | 10 => 2145632773798401 / 4000000000000
    | 11 => 3807463009363509 / 4000000000000
    | 12 => 3557425834458921 / 4000000000000
    | 13 => 2538746935004793 / 4000000000000
    | 14 => 2878668442178847 / 4000000000000
    | 15 => 2399933630816943 / 4000000000000
    | 16 => 2120414145511803 / 4000000000000
    | 17 => 614578666480497 / 800000000000
    | 18 => 1699956934988259 / 4000000000000
    | 19 => 1441072320297099 / 4000000000000
    | 20 => 901756146908697 / 4000000000000
    | 21 => 484967454912999 / 4000000000000
    | 22 => 1316780979695997 / 4000000000000
    | 23 => 1797951852706269 / 4000000000000
    | 24 => 760243853091303 / 4000000000000
    | 25 => 3090349055339463 / 4000000000000
    | _ => 2064209949633417 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))
    | 1 => (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))
    | 2 => (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000))
    | 3 => (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))
    | 4 => (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
    | 5 => (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000))
    | 6 => (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))
    | 7 => (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))
    | 8 => (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000))
    | 9 => (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))
    | 10 => (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))
    | 11 => (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000))
    | 12 => (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))
    | 13 => (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))
    | 14 => (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000))
    | 15 => (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))
    | 16 => (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))
    | 17 => (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000))
    | 18 => (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))
    | 19 => (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))
    | 20 => (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000))
    | 21 => (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))
    | 22 => (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))
    | 23 => (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000))
    | 24 => (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))
    | 25 => (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))
    | _ => (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13747057740 / 1000000000000) (13747058783 / 1000000000000)
      | 1 => orderedInterval (3146655297 / 1000000000000) (3146657110 / 1000000000000)
      | 2 => orderedInterval (159277112 / 1000000000000) (159277136 / 1000000000000)
      | 3 => orderedInterval (-2267686357 / 1000000000000) (-2267686192 / 1000000000000)
      | 4 => orderedInterval (2842278394 / 1000000000000) (2842278444 / 1000000000000)
      | 5 => orderedInterval (134905050 / 1000000000000) (134905112 / 1000000000000)
      | 6 => orderedInterval (5672220583 / 1000000000000) (5672220846 / 1000000000000)
      | 7 => orderedInterval (1941581175 / 1000000000000) (1941581303 / 1000000000000)
      | _ => orderedInterval (-7537762499 / 1000000000000) (-7537761879 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1643762357 / 1000000000000) (1643763353 / 1000000000000)
      | 1 => orderedInterval (-1126746116 / 1000000000000) (-1126743833 / 1000000000000)
      | 2 => orderedInterval (-2805054247 / 1000000000000) (-2805054206 / 1000000000000)
      | 3 => orderedInterval (-19855444580 / 1000000000000) (-19855444238 / 1000000000000)
      | 4 => orderedInterval (3575966475 / 1000000000000) (3575966556 / 1000000000000)
      | 5 => orderedInterval (1062904874 / 1000000000000) (1062904972 / 1000000000000)
      | 6 => orderedInterval (2380424642 / 1000000000000) (2380424900 / 1000000000000)
      | 7 => orderedInterval (2745252183 / 1000000000000) (2745252251 / 1000000000000)
      | _ => orderedInterval (-3454621681 / 1000000000000) (-3454621139 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13333282827 / 1000000000000) (-13333281828 / 1000000000000)
      | 1 => orderedInterval (-5843614822 / 1000000000000) (-5843611440 / 1000000000000)
      | 2 => orderedInterval (-643137496 / 1000000000000) (-643137423 / 1000000000000)
      | 3 => orderedInterval (12168644376 / 1000000000000) (12168645109 / 1000000000000)
      | 4 => orderedInterval (-7679551480 / 1000000000000) (-7679551346 / 1000000000000)
      | 5 => orderedInterval (-939738847 / 1000000000000) (-939738687 / 1000000000000)
      | 6 => orderedInterval (-6061705205 / 1000000000000) (-6061704948 / 1000000000000)
      | 7 => orderedInterval (-2908616925 / 1000000000000) (-2908616873 / 1000000000000)
      | _ => orderedInterval (14269953164 / 1000000000000) (14269953764 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2323415188 / 1000000000000) (-2323414148 / 1000000000000)
      | 1 => orderedInterval (2257014377 / 1000000000000) (2257019589 / 1000000000000)
      | 2 => orderedInterval (8938144605 / 1000000000000) (8938144736 / 1000000000000)
      | 3 => orderedInterval (89796368933 / 1000000000000) (89796370540 / 1000000000000)
      | 4 => orderedInterval (-9527917253 / 1000000000000) (-9527917026 / 1000000000000)
      | 5 => orderedInterval (354157305 / 1000000000000) (354157573 / 1000000000000)
      | 6 => orderedInterval (-1178936040 / 1000000000000) (-1178935782 / 1000000000000)
      | 7 => orderedInterval (-2406188703 / 1000000000000) (-2406188655 / 1000000000000)
      | _ => orderedInterval (12274848464 / 1000000000000) (12274849228 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12601418654 / 1000000000000) (12601419777 / 1000000000000)
      | 1 => orderedInterval (13188166990 / 1000000000000) (13188175125 / 1000000000000)
      | 2 => orderedInterval (2557143730 / 1000000000000) (2557143974 / 1000000000000)
      | 3 => orderedInterval (-64564282518 / 1000000000000) (-64564278950 / 1000000000000)
      | 4 => orderedInterval (22568863210 / 1000000000000) (22568863605 / 1000000000000)
      | 5 => orderedInterval (4128864594 / 1000000000000) (4128865056 / 1000000000000)
      | 6 => orderedInterval (6450267793 / 1000000000000) (6450268054 / 1000000000000)
      | 7 => orderedInterval (3428259460 / 1000000000000) (3428259509 / 1000000000000)
      | _ => orderedInterval (-30090904345 / 1000000000000) (-30090903284 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17838526495 / 1000000000000) (17838530663 / 1000000000000)
    | 1 => orderedInterval (-15833556093 / 1000000000000) (-15833551384 / 1000000000000)
    | 2 => orderedInterval (-10971050062 / 1000000000000) (-10971043672 / 1000000000000)
    | 3 => orderedInterval (98184076500 / 1000000000000) (98184086055 / 1000000000000)
    | _ => orderedInterval (-29732202432 / 1000000000000) (-29732187134 / 1000000000000)

theorem compactCertificate544_stateChecks0 :
    compactCertificate544.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (831 / 2)) (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1224221677705731 / 4000000000000)) (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (395888137348323 / 800000000000)) (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks1 :
    compactCertificate544.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (357224832302217 / 4000000000000)) (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (959556147392949 / 4000000000000)) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2605381600425633 / 4000000000000)) (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks2 :
    compactCertificate544.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1919112294786729 / 4000000000000)) (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3288431627338317 / 4000000000000)) (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2422243853091303 / 4000000000000)) (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks3 :
    compactCertificate544.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3716344978604169 / 4000000000000)) (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2145632773798401 / 4000000000000)) (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 303 12 (3807463009363509 / 4000000000000)) (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks4 :
    compactCertificate544.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (3557425834458921 / 4000000000000)) (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2538746935004793 / 4000000000000)) (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2878668442178847 / 4000000000000)) (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks5 :
    compactCertificate544.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2399933630816943 / 4000000000000)) (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2120414145511803 / 4000000000000)) (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (614578666480497 / 800000000000)) (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks6 :
    compactCertificate544.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1699956934988259 / 4000000000000)) (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1441072320297099 / 4000000000000)) (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (901756146908697 / 4000000000000)) (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks7 :
    compactCertificate544.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (484967454912999 / 4000000000000)) (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1316780979695997 / 4000000000000)) (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1797951852706269 / 4000000000000)) (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_stateChecks8 :
    compactCertificate544.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (760243853091303 / 4000000000000)) (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3090349055339463 / 4000000000000)) (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2064209949633417 / 4000000000000)) (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_states : ∀ j,
    BesselStateValid (compactCertificate544.point j) (compactCertificate544.state j) :=
  compactCertificate544.statesValid_of_checks3 compactCertificate544_stateChecks0
    compactCertificate544_stateChecks1 compactCertificate544_stateChecks2
    compactCertificate544_stateChecks3 compactCertificate544_stateChecks4
    compactCertificate544_stateChecks5 compactCertificate544_stateChecks6
    compactCertificate544_stateChecks7 compactCertificate544_stateChecks8

theorem compactCertificate544_chunkChecks0_0 :
    compactCertificate544.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (831 / 2) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1224221677705731 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (395888137348323 / 800000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000)))) (orderedInterval (13747057740 / 1000000000000) (13747058783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (357224832302217 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2605381600425633 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000)))) (orderedInterval (3146655297 / 1000000000000) (3146657110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1919112294786729 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3288431627338317 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2422243853091303 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000)))) (orderedInterval (159277112 / 1000000000000) (159277136 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks0_1 :
    compactCertificate544.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3716344978604169 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2145632773798401 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3807463009363509 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000)))) (orderedInterval (-2267686357 / 1000000000000) (-2267686192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3557425834458921 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2538746935004793 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2878668442178847 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000)))) (orderedInterval (2842278394 / 1000000000000) (2842278444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2399933630816943 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2120414145511803 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (614578666480497 / 800000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000)))) (orderedInterval (134905050 / 1000000000000) (134905112 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks0_2 :
    compactCertificate544.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1699956934988259 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1441072320297099 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (901756146908697 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000)))) (orderedInterval (5672220583 / 1000000000000) (5672220846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (484967454912999 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1316780979695997 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1797951852706269 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000)))) (orderedInterval (1941581175 / 1000000000000) (1941581303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (760243853091303 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3090349055339463 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2064209949633417 / 4000000000000) 0 (IntervalRat.scale (831 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000)))) (orderedInterval (-7537762499 / 1000000000000) (-7537761879 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks0 :
    compactCertificate544.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate544.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate544_chunkChecks0_0
    compactCertificate544_chunkChecks0_1 compactCertificate544_chunkChecks0_2

theorem compactCertificate544_chunkChecks1_0 :
    compactCertificate544.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (831 / 2) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1224221677705731 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (395888137348323 / 800000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000)))) (orderedInterval (1643762357 / 1000000000000) (1643763353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (357224832302217 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2605381600425633 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000)))) (orderedInterval (-1126746116 / 1000000000000) (-1126743833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1919112294786729 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3288431627338317 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2422243853091303 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000)))) (orderedInterval (-2805054247 / 1000000000000) (-2805054206 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks1_1 :
    compactCertificate544.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3716344978604169 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2145632773798401 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3807463009363509 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000)))) (orderedInterval (-19855444580 / 1000000000000) (-19855444238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3557425834458921 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2538746935004793 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2878668442178847 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000)))) (orderedInterval (3575966475 / 1000000000000) (3575966556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2399933630816943 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2120414145511803 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (614578666480497 / 800000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000)))) (orderedInterval (1062904874 / 1000000000000) (1062904972 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks1_2 :
    compactCertificate544.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1699956934988259 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1441072320297099 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (901756146908697 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000)))) (orderedInterval (2380424642 / 1000000000000) (2380424900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (484967454912999 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1316780979695997 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1797951852706269 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000)))) (orderedInterval (2745252183 / 1000000000000) (2745252251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (760243853091303 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3090349055339463 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2064209949633417 / 4000000000000) 1 (IntervalRat.scale (831 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000)))) (orderedInterval (-3454621681 / 1000000000000) (-3454621139 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks1 :
    compactCertificate544.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate544.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate544_chunkChecks1_0
    compactCertificate544_chunkChecks1_1 compactCertificate544_chunkChecks1_2

theorem compactCertificate544_chunkChecks2_0 :
    compactCertificate544.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (831 / 2) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1224221677705731 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (395888137348323 / 800000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000)))) (orderedInterval (-13333282827 / 1000000000000) (-13333281828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (357224832302217 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2605381600425633 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000)))) (orderedInterval (-5843614822 / 1000000000000) (-5843611440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1919112294786729 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3288431627338317 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2422243853091303 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000)))) (orderedInterval (-643137496 / 1000000000000) (-643137423 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks2_1 :
    compactCertificate544.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3716344978604169 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2145632773798401 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3807463009363509 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000)))) (orderedInterval (12168644376 / 1000000000000) (12168645109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3557425834458921 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2538746935004793 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2878668442178847 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000)))) (orderedInterval (-7679551480 / 1000000000000) (-7679551346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2399933630816943 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2120414145511803 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (614578666480497 / 800000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000)))) (orderedInterval (-939738847 / 1000000000000) (-939738687 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks2_2 :
    compactCertificate544.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1699956934988259 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1441072320297099 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (901756146908697 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000)))) (orderedInterval (-6061705205 / 1000000000000) (-6061704948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (484967454912999 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1316780979695997 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1797951852706269 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000)))) (orderedInterval (-2908616925 / 1000000000000) (-2908616873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (760243853091303 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3090349055339463 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2064209949633417 / 4000000000000) 2 (IntervalRat.scale (831 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000)))) (orderedInterval (14269953164 / 1000000000000) (14269953764 / 1000000000000))) = true
  rfl'

theorem compactCertificate544_chunkChecks2 :
    compactCertificate544.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate544.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate544_chunkChecks2_0
    compactCertificate544_chunkChecks2_1 compactCertificate544_chunkChecks2_2

theorem compactCertificate544_chunkChecks3_0 :
    compactCertificate544.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (831 / 2) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1224221677705731 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (395888137348323 / 800000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000)))) (orderedInterval (-2323415188 / 1000000000000) (-2323414148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (357224832302217 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2605381600425633 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000)))) (orderedInterval (2257014377 / 1000000000000) (2257019589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1919112294786729 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3288431627338317 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2422243853091303 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000)))) (orderedInterval (8938144605 / 1000000000000) (8938144736 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate544_chunkChecks3_1 :
    compactCertificate544.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3716344978604169 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2145632773798401 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3807463009363509 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000)))) (orderedInterval (89796368933 / 1000000000000) (89796370540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3557425834458921 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2538746935004793 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2878668442178847 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000)))) (orderedInterval (-9527917253 / 1000000000000) (-9527917026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2399933630816943 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2120414145511803 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (614578666480497 / 800000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000)))) (orderedInterval (354157305 / 1000000000000) (354157573 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate544_chunkChecks3_2 :
    compactCertificate544.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1699956934988259 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1441072320297099 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (901756146908697 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000)))) (orderedInterval (-1178936040 / 1000000000000) (-1178935782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (484967454912999 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1316780979695997 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1797951852706269 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000)))) (orderedInterval (-2406188703 / 1000000000000) (-2406188655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (760243853091303 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3090349055339463 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2064209949633417 / 4000000000000) 3 (IntervalRat.scale (831 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000)))) (orderedInterval (12274848464 / 1000000000000) (12274849228 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate544_chunkChecks3 :
    compactCertificate544.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate544.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate544_chunkChecks3_0
    compactCertificate544_chunkChecks3_1 compactCertificate544_chunkChecks3_2

theorem compactCertificate544_chunkChecks4_0 :
    compactCertificate544.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (831 / 2) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39131686057 / 1000000000000) (39131686473 / 1000000000000), orderedInterval (-989200566 / 1000000000000) (-989200150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1224221677705731 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39232121945 / 1000000000000) (-39232071519 / 1000000000000), orderedInterval (23321780496 / 1000000000000) (23321830923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (395888137348323 / 800000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23820352663 / 1000000000000) (-23820346194 / 1000000000000), orderedInterval (26839264950 / 1000000000000) (26839271420 / 1000000000000)))) (orderedInterval (12601418654 / 1000000000000) (12601419777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (357224832302217 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71765108368 / 1000000000000) (71765130783 / 1000000000000), orderedInterval (-44879009945 / 1000000000000) (-44878987530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2605381600425633 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30290362611 / 1000000000000) (-30290344197 / 1000000000000), orderedInterval (7761860637 / 1000000000000) (7761879051 / 1000000000000)))) (orderedInterval (13188166990 / 1000000000000) (13188175125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1919112294786729 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3653442860 / 1000000000000) (3653442862 / 1000000000000), orderedInterval (-36246844599 / 1000000000000) (-36246844597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3288431627338317 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5640868339 / 1000000000000) (-5640868337 / 1000000000000), orderedInterval (27253305772 / 1000000000000) (27253305773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2422243853091303 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-608648137 / 1000000000000) (-608648136 / 1000000000000), orderedInterval (-32417381775 / 1000000000000) (-32417381774 / 1000000000000)))) (orderedInterval (2557143730 / 1000000000000) (2557143974 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate544_chunkChecks4_1 :
    compactCertificate544.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3716344978604169 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1044615883 / 1000000000000) (-1044615882 / 1000000000000), orderedInterval (26156240486 / 1000000000000) (26156240487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2145632773798401 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (654004805 / 1000000000000) (654004806 / 1000000000000), orderedInterval (-34444657293 / 1000000000000) (-34444657292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3807463009363509 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17598695649 / 1000000000000) (-17598695648 / 1000000000000), orderedInterval (-18940649622 / 1000000000000) (-18940649621 / 1000000000000)))) (orderedInterval (-64564282518 / 1000000000000) (-64564278950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3557425834458921 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23482118092 / 1000000000000) (-23482118085 / 1000000000000), orderedInterval (-12809074959 / 1000000000000) (-12809074952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2538746935004793 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24211449278 / 1000000000000) (24211449279 / 1000000000000), orderedInterval (20397863778 / 1000000000000) (20397863779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2878668442178847 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25461466808 / 1000000000000) (-25461466806 / 1000000000000), orderedInterval (-15354906980 / 1000000000000) (-15354906978 / 1000000000000)))) (orderedInterval (22568863210 / 1000000000000) (22568863605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2399933630816943 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21586321869 / 1000000000000) (-21586321868 / 1000000000000), orderedInterval (-24376540001 / 1000000000000) (-24376540000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2120414145511803 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1401728710 / 1000000000000) (1401728711 / 1000000000000), orderedInterval (-34627475051 / 1000000000000) (-34627475049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (614578666480497 / 800000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18137555657 / 1000000000000) (18137556497 / 1000000000000), orderedInterval (-22366225620 / 1000000000000) (-22366224780 / 1000000000000)))) (orderedInterval (4128864594 / 1000000000000) (4128865056 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate544_chunkChecks4_2 :
    compactCertificate544.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1699956934988259 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38551980676 / 1000000000000) (-38551979699 / 1000000000000), orderedInterval (3467434927 / 1000000000000) (3467435903 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1441072320297099 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (9584363922 / 1000000000000) (9584363953 / 1000000000000), orderedInterval (-40942678303 / 1000000000000) (-40942678273 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (901756146908697 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (1551977115 / 1000000000000) (1551977117 / 1000000000000), orderedInterval (53114438932 / 1000000000000) (53114438934 / 1000000000000)))) (orderedInterval (6450267793 / 1000000000000) (6450268054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (484967454912999 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (34478130390 / 1000000000000) (34478134568 / 1000000000000), orderedInterval (-63876851812 / 1000000000000) (-63876847635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1316780979695997 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-4960206906 / 1000000000000) (-4960206905 / 1000000000000), orderedInterval (-43687607494 / 1000000000000) (-43687607493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1797951852706269 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32172870760 / 1000000000000) (-32172870759 / 1000000000000), orderedInterval (-19489276697 / 1000000000000) (-19489276696 / 1000000000000)))) (orderedInterval (3428259460 / 1000000000000) (3428259509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (760243853091303 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41170788695 / 1000000000000) (41170840753 / 1000000000000), orderedInterval (-40784118100 / 1000000000000) (-40784066043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3090349055339463 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14775982775 / 1000000000000) (14775982776 / 1000000000000), orderedInterval (24601016301 / 1000000000000) (24601016302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2064209949633417 / 4000000000000) 4 (IntervalRat.scale (831 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35086520649 / 1000000000000) (35086521665 / 1000000000000), orderedInterval (-1636874010 / 1000000000000) (-1636872995 / 1000000000000)))) (orderedInterval (-30090904345 / 1000000000000) (-30090903284 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate544_chunkChecks4 :
    compactCertificate544.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate544.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate544_chunkChecks4_0
    compactCertificate544_chunkChecks4_1 compactCertificate544_chunkChecks4_2

theorem compactCertificate544_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate544.chunkCheck r b = true :=
  compactCertificate544.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate544_chunkChecks0
    · exact compactCertificate544_chunkChecks1
    · exact compactCertificate544_chunkChecks2
    · exact compactCertificate544_chunkChecks3
    · exact compactCertificate544_chunkChecks4)

theorem compactCertificate544_coefficient0 :
    compactCertificate544.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate544_coefficient1 :
    compactCertificate544.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate544_coefficient2 :
    compactCertificate544.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate544_coefficient3 :
    compactCertificate544.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate544_coefficient4 :
    compactCertificate544.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate544_coefficients : ∀ r : Fin 5,
    compactCertificate544.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate544_coefficient0
  · exact compactCertificate544_coefficient1
  · exact compactCertificate544_coefficient2
  · exact compactCertificate544_coefficient3
  · exact compactCertificate544_coefficient4

theorem compactCertificate544_lower : (1 : ℚ) ≤ compactCertificate544.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate544, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate544_proves {t : ℝ} (ht : t ∈ compactCertificate544.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate544.proves compactCertificate544_states compactCertificate544_chunks
    compactCertificate544_coefficients compactCertificate544_lower ht

end Erdos232
