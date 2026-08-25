/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate363 : CompactCertificate where
  left := 234
  right := 235
  center := 469 / 2
  grid := fun i =>
    match i.val with
    | 0 => 75
    | 1 => 55
    | 2 => 89
    | 3 => 16
    | 4 => 43
    | 5 => 117
    | 6 => 86
    | 7 => 148
    | 8 => 109
    | 9 => 167
    | 10 => 96
    | 11 => 171
    | 12 => 160
    | 13 => 114
    | 14 => 129
    | 15 => 108
    | 16 => 95
    | 17 => 138
    | 18 => 76
    | 19 => 65
    | 20 => 41
    | 21 => 22
    | 22 => 59
    | 23 => 81
    | 24 => 34
    | 25 => 139
    | _ => 93
  point := fun i =>
    match i.val with
    | 0 => 469 / 2
    | 1 => 690926554565569 / 4000000000000
    | 2 => 223431451764577 / 800000000000
    | 3 => 201610645426883 / 4000000000000
    | 4 => 541554552499751 / 4000000000000
    | 5 => 1470425957400267 / 4000000000000
    | 6 => 1083109104999971 / 4000000000000
    | 7 => 1855925912420783 / 4000000000000
    | 8 => 1367066627075597 / 4000000000000
    | 9 => 2097431762894531 / 4000000000000
    | 10 => 1210952792913899 / 4000000000000
    | 11 => 2148856981217191 / 4000000000000
    | 12 => 2007740934249379 / 4000000000000
    | 13 => 1432818667289107 / 4000000000000
    | 14 => 1624663657499253 / 4000000000000
    | 15 => 1354475177921957 / 4000000000000
    | 16 => 1196719896805097 / 4000000000000
    | 17 => 346856070492603 / 800000000000
    | 18 => 959422145017441 / 4000000000000
    | 19 => 813312777640601 / 4000000000000
    | 20 => 508933372924403 / 4000000000000
    | 21 => 273706060594701 / 4000000000000
    | 22 => 743165197927103 / 4000000000000
    | 23 => 1014728542622431 / 4000000000000
    | 24 => 429066627075597 / 4000000000000
    | 25 => 1744132017995437 / 4000000000000
    | _ => 1164999357855683 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))
    | 1 => (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))
    | 2 => (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000))
    | 3 => (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))
    | 4 => (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))
    | 5 => (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000))
    | 6 => (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))
    | 7 => (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))
    | 8 => (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000))
    | 9 => (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))
    | 10 => (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))
    | 11 => (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000))
    | 12 => (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))
    | 13 => (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))
    | 14 => (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000))
    | 15 => (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))
    | 16 => (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))
    | 17 => (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000))
    | 18 => (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))
    | 19 => (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))
    | 20 => (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000))
    | 21 => (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))
    | 22 => (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))
    | 23 => (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000))
    | 24 => (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))
    | 25 => (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))
    | _ => (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5129835501 / 1000000000000) (5129835646 / 1000000000000)
      | 1 => orderedInterval (-1010229513 / 1000000000000) (-1010229485 / 1000000000000)
      | 2 => orderedInterval (91879303 / 1000000000000) (91879317 / 1000000000000)
      | 3 => orderedInterval (2667010967 / 1000000000000) (2667011768 / 1000000000000)
      | 4 => orderedInterval (3147049542 / 1000000000000) (3147049576 / 1000000000000)
      | 5 => orderedInterval (3405622600 / 1000000000000) (3405622626 / 1000000000000)
      | 6 => orderedInterval (-6502919982 / 1000000000000) (-6502917117 / 1000000000000)
      | 7 => orderedInterval (1071499047 / 1000000000000) (1071499076 / 1000000000000)
      | _ => orderedInterval (-303207989 / 1000000000000) (-303207921 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-22799808502 / 1000000000000) (-22799808355 / 1000000000000)
      | 1 => orderedInterval (2314181950 / 1000000000000) (2314181983 / 1000000000000)
      | 2 => orderedInterval (-3730090313 / 1000000000000) (-3730090289 / 1000000000000)
      | 3 => orderedInterval (2705707503 / 1000000000000) (2705708611 / 1000000000000)
      | 4 => orderedInterval (2607766520 / 1000000000000) (2607766577 / 1000000000000)
      | 5 => orderedInterval (2147201969 / 1000000000000) (2147202006 / 1000000000000)
      | 6 => orderedInterval (4425954372 / 1000000000000) (4425956261 / 1000000000000)
      | 7 => orderedInterval (3993158684 / 1000000000000) (3993158711 / 1000000000000)
      | _ => orderedInterval (16598089356 / 1000000000000) (16598089450 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-4671314851 / 1000000000000) (-4671314701 / 1000000000000)
      | 1 => orderedInterval (-4568382455 / 1000000000000) (-4568382410 / 1000000000000)
      | 2 => orderedInterval (-563855477 / 1000000000000) (-563855435 / 1000000000000)
      | 3 => orderedInterval (-1884893950 / 1000000000000) (-1884892351 / 1000000000000)
      | 4 => orderedInterval (-7392231543 / 1000000000000) (-7392231449 / 1000000000000)
      | 5 => orderedInterval (-6857168460 / 1000000000000) (-6857168405 / 1000000000000)
      | 6 => orderedInterval (7926984341 / 1000000000000) (7926985716 / 1000000000000)
      | 7 => orderedInterval (-777248817 / 1000000000000) (-777248791 / 1000000000000)
      | _ => orderedInterval (170061728 / 1000000000000) (170061867 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (23919700005 / 1000000000000) (23919700159 / 1000000000000)
      | 1 => orderedInterval (-7469809391 / 1000000000000) (-7469809323 / 1000000000000)
      | 2 => orderedInterval (11902193992 / 1000000000000) (11902194068 / 1000000000000)
      | 3 => orderedInterval (-16724429688 / 1000000000000) (-16724427251 / 1000000000000)
      | 4 => orderedInterval (-2939401159 / 1000000000000) (-2939400999 / 1000000000000)
      | 5 => orderedInterval (-6018651128 / 1000000000000) (-6018651046 / 1000000000000)
      | 6 => orderedInterval (-4524292044 / 1000000000000) (-4524290947 / 1000000000000)
      | 7 => orderedInterval (-5037173369 / 1000000000000) (-5037173342 / 1000000000000)
      | _ => orderedInterval (-36482025911 / 1000000000000) (-36482025698 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (3901035543 / 1000000000000) (3901035702 / 1000000000000)
      | 1 => orderedInterval (12941194788 / 1000000000000) (12941194891 / 1000000000000)
      | 2 => orderedInterval (2635607418 / 1000000000000) (2635607559 / 1000000000000)
      | 3 => orderedInterval (-12674426686 / 1000000000000) (-12674422688 / 1000000000000)
      | 4 => orderedInterval (17211754827 / 1000000000000) (17211755103 / 1000000000000)
      | 5 => orderedInterval (15623572197 / 1000000000000) (15623572325 / 1000000000000)
      | 6 => orderedInterval (-8571988900 / 1000000000000) (-8571987943 / 1000000000000)
      | 7 => orderedInterval (523172413 / 1000000000000) (523172441 / 1000000000000)
      | _ => orderedInterval (2624183190 / 1000000000000) (2624183531 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7696539476 / 1000000000000) (7696543486 / 1000000000000)
    | 1 => orderedInterval (8262161539 / 1000000000000) (8262164955 / 1000000000000)
    | 2 => orderedInterval (-18618049484 / 1000000000000) (-18618045959 / 1000000000000)
    | 3 => orderedInterval (-43373888693 / 1000000000000) (-43373884379 / 1000000000000)
    | _ => orderedInterval (34214104790 / 1000000000000) (34214110921 / 1000000000000)

theorem compactCertificate363_stateChecks0 :
    compactCertificate363.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (469 / 2)) (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (690926554565569 / 4000000000000)) (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (223431451764577 / 800000000000)) (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks1 :
    compactCertificate363.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (201610645426883 / 4000000000000)) (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (541554552499751 / 4000000000000)) (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1470425957400267 / 4000000000000)) (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks2 :
    compactCertificate363.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1083109104999971 / 4000000000000)) (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1855925912420783 / 4000000000000)) (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1367066627075597 / 4000000000000)) (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks3 :
    compactCertificate363.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2097431762894531 / 4000000000000)) (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1210952792913899 / 4000000000000)) (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2148856981217191 / 4000000000000)) (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks4 :
    compactCertificate363.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2007740934249379 / 4000000000000)) (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1432818667289107 / 4000000000000)) (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1624663657499253 / 4000000000000)) (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks5 :
    compactCertificate363.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1354475177921957 / 4000000000000)) (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1196719896805097 / 4000000000000)) (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (346856070492603 / 800000000000)) (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks6 :
    compactCertificate363.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (959422145017441 / 4000000000000)) (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (813312777640601 / 4000000000000)) (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (508933372924403 / 4000000000000)) (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks7 :
    compactCertificate363.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (273706060594701 / 4000000000000)) (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (743165197927103 / 4000000000000)) (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1014728542622431 / 4000000000000)) (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_stateChecks8 :
    compactCertificate363.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (429066627075597 / 4000000000000)) (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1744132017995437 / 4000000000000)) (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1164999357855683 / 4000000000000)) (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_states : ∀ j,
    BesselStateValid (compactCertificate363.point j) (compactCertificate363.state j) :=
  compactCertificate363.statesValid_of_checks3 compactCertificate363_stateChecks0
    compactCertificate363_stateChecks1 compactCertificate363_stateChecks2
    compactCertificate363_stateChecks3 compactCertificate363_stateChecks4
    compactCertificate363_stateChecks5 compactCertificate363_stateChecks6
    compactCertificate363_stateChecks7 compactCertificate363_stateChecks8

theorem compactCertificate363_chunkChecks0_0 :
    compactCertificate363.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (469 / 2) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (690926554565569 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (223431451764577 / 800000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000)))) (orderedInterval (5129835501 / 1000000000000) (5129835646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (201610645426883 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (541554552499751 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1470425957400267 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000)))) (orderedInterval (-1010229513 / 1000000000000) (-1010229485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1083109104999971 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1855925912420783 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1367066627075597 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000)))) (orderedInterval (91879303 / 1000000000000) (91879317 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks0_1 :
    compactCertificate363.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2097431762894531 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1210952792913899 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2148856981217191 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000)))) (orderedInterval (2667010967 / 1000000000000) (2667011768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2007740934249379 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1432818667289107 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1624663657499253 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000)))) (orderedInterval (3147049542 / 1000000000000) (3147049576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1354475177921957 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1196719896805097 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (346856070492603 / 800000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000)))) (orderedInterval (3405622600 / 1000000000000) (3405622626 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks0_2 :
    compactCertificate363.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (959422145017441 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (813312777640601 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (508933372924403 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000)))) (orderedInterval (-6502919982 / 1000000000000) (-6502917117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (273706060594701 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (743165197927103 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1014728542622431 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000)))) (orderedInterval (1071499047 / 1000000000000) (1071499076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (429066627075597 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1744132017995437 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1164999357855683 / 4000000000000) 0 (IntervalRat.scale (469 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000)))) (orderedInterval (-303207989 / 1000000000000) (-303207921 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks0 :
    compactCertificate363.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate363.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate363_chunkChecks0_0
    compactCertificate363_chunkChecks0_1 compactCertificate363_chunkChecks0_2

theorem compactCertificate363_chunkChecks1_0 :
    compactCertificate363.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (469 / 2) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (690926554565569 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (223431451764577 / 800000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000)))) (orderedInterval (-22799808502 / 1000000000000) (-22799808355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (201610645426883 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (541554552499751 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1470425957400267 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000)))) (orderedInterval (2314181950 / 1000000000000) (2314181983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1083109104999971 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1855925912420783 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1367066627075597 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000)))) (orderedInterval (-3730090313 / 1000000000000) (-3730090289 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks1_1 :
    compactCertificate363.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2097431762894531 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1210952792913899 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2148856981217191 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000)))) (orderedInterval (2705707503 / 1000000000000) (2705708611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2007740934249379 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1432818667289107 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1624663657499253 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000)))) (orderedInterval (2607766520 / 1000000000000) (2607766577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1354475177921957 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1196719896805097 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (346856070492603 / 800000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000)))) (orderedInterval (2147201969 / 1000000000000) (2147202006 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks1_2 :
    compactCertificate363.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (959422145017441 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (813312777640601 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (508933372924403 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000)))) (orderedInterval (4425954372 / 1000000000000) (4425956261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (273706060594701 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (743165197927103 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1014728542622431 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000)))) (orderedInterval (3993158684 / 1000000000000) (3993158711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (429066627075597 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1744132017995437 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1164999357855683 / 4000000000000) 1 (IntervalRat.scale (469 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000)))) (orderedInterval (16598089356 / 1000000000000) (16598089450 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks1 :
    compactCertificate363.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate363.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate363_chunkChecks1_0
    compactCertificate363_chunkChecks1_1 compactCertificate363_chunkChecks1_2

theorem compactCertificate363_chunkChecks2_0 :
    compactCertificate363.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (469 / 2) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (690926554565569 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (223431451764577 / 800000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000)))) (orderedInterval (-4671314851 / 1000000000000) (-4671314701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (201610645426883 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (541554552499751 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1470425957400267 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000)))) (orderedInterval (-4568382455 / 1000000000000) (-4568382410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1083109104999971 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1855925912420783 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1367066627075597 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000)))) (orderedInterval (-563855477 / 1000000000000) (-563855435 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks2_1 :
    compactCertificate363.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2097431762894531 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1210952792913899 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2148856981217191 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000)))) (orderedInterval (-1884893950 / 1000000000000) (-1884892351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2007740934249379 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1432818667289107 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1624663657499253 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000)))) (orderedInterval (-7392231543 / 1000000000000) (-7392231449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1354475177921957 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1196719896805097 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (346856070492603 / 800000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000)))) (orderedInterval (-6857168460 / 1000000000000) (-6857168405 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks2_2 :
    compactCertificate363.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (959422145017441 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (813312777640601 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (508933372924403 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000)))) (orderedInterval (7926984341 / 1000000000000) (7926985716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (273706060594701 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (743165197927103 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1014728542622431 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000)))) (orderedInterval (-777248817 / 1000000000000) (-777248791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (429066627075597 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1744132017995437 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1164999357855683 / 4000000000000) 2 (IntervalRat.scale (469 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000)))) (orderedInterval (170061728 / 1000000000000) (170061867 / 1000000000000))) = true
  rfl'

theorem compactCertificate363_chunkChecks2 :
    compactCertificate363.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate363.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate363_chunkChecks2_0
    compactCertificate363_chunkChecks2_1 compactCertificate363_chunkChecks2_2

theorem compactCertificate363_chunkChecks3_0 :
    compactCertificate363.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (469 / 2) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (690926554565569 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (223431451764577 / 800000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000)))) (orderedInterval (23919700005 / 1000000000000) (23919700159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (201610645426883 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (541554552499751 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1470425957400267 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000)))) (orderedInterval (-7469809391 / 1000000000000) (-7469809323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1083109104999971 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1855925912420783 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1367066627075597 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000)))) (orderedInterval (11902193992 / 1000000000000) (11902194068 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate363_chunkChecks3_1 :
    compactCertificate363.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2097431762894531 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1210952792913899 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2148856981217191 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000)))) (orderedInterval (-16724429688 / 1000000000000) (-16724427251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2007740934249379 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1432818667289107 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1624663657499253 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000)))) (orderedInterval (-2939401159 / 1000000000000) (-2939400999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1354475177921957 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1196719896805097 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (346856070492603 / 800000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000)))) (orderedInterval (-6018651128 / 1000000000000) (-6018651046 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate363_chunkChecks3_2 :
    compactCertificate363.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (959422145017441 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (813312777640601 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (508933372924403 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000)))) (orderedInterval (-4524292044 / 1000000000000) (-4524290947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (273706060594701 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (743165197927103 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1014728542622431 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000)))) (orderedInterval (-5037173369 / 1000000000000) (-5037173342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (429066627075597 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1744132017995437 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1164999357855683 / 4000000000000) 3 (IntervalRat.scale (469 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000)))) (orderedInterval (-36482025911 / 1000000000000) (-36482025698 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate363_chunkChecks3 :
    compactCertificate363.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate363.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate363_chunkChecks3_0
    compactCertificate363_chunkChecks3_1 compactCertificate363_chunkChecks3_2

theorem compactCertificate363_chunkChecks4_0 :
    compactCertificate363.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (469 / 2) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17109596836 / 1000000000000) (17109597158 / 1000000000000), orderedInterval (-49250940276 / 1000000000000) (-49250939954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (690926554565569 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40426934971 / 1000000000000) (-40426934970 / 1000000000000), orderedInterval (-45173871018 / 1000000000000) (-45173871017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (223431451764577 / 800000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21729453707 / 1000000000000) (-21729453706 / 1000000000000), orderedInterval (-42472986320 / 1000000000000) (-42472986319 / 1000000000000)))) (orderedInterval (3901035543 / 1000000000000) (3901035702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (201610645426883 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89419155133 / 1000000000000) (89419155134 / 1000000000000), orderedInterval (67191869548 / 1000000000000) (67191869549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (541554552499751 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60626660717 / 1000000000000) (-60626660716 / 1000000000000), orderedInterval (-31816007146 / 1000000000000) (-31816007145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1470425957400267 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30573936545 / 1000000000000) (-30573936544 / 1000000000000), orderedInterval (-28190155222 / 1000000000000) (-28190155221 / 1000000000000)))) (orderedInterval (12941194788 / 1000000000000) (12941194891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1083109104999971 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47655609041 / 1000000000000) (47655609048 / 1000000000000), orderedInterval (8857498627 / 1000000000000) (8857498634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1855925912420783 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6963106854 / 1000000000000) (-6963106846 / 1000000000000), orderedInterval (36388762896 / 1000000000000) (36388762903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1367066627075597 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5084848861 / 1000000000000) (-5084848860 / 1000000000000), orderedInterval (-42851381475 / 1000000000000) (-42851381474 / 1000000000000)))) (orderedInterval (2635607418 / 1000000000000) (2635607559 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate363_chunkChecks4_1 :
    compactCertificate363.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2097431762894531 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16617118150 / 1000000000000) (-16617118149 / 1000000000000), orderedInterval (-30610378475 / 1000000000000) (-30610378474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1210952792913899 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42925660566 / 1000000000000) (42925670121 / 1000000000000), orderedInterval (-16203394871 / 1000000000000) (-16203385316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2148856981217191 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24382306006 / 1000000000000) (-24382306005 / 1000000000000), orderedInterval (-24278377521 / 1000000000000) (-24278377520 / 1000000000000)))) (orderedInterval (-12674426686 / 1000000000000) (-12674422688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2007740934249379 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2333089724 / 1000000000000) (2333089725 / 1000000000000), orderedInterval (35534809013 / 1000000000000) (35534809014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1432818667289107 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31620629491 / 1000000000000) (31620629492 / 1000000000000), orderedInterval (27837523938 / 1000000000000) (27837523939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1624663657499253 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39329847424 / 1000000000000) (-39329846234 / 1000000000000), orderedInterval (4581677223 / 1000000000000) (4581678413 / 1000000000000)))) (orderedInterval (17211754827 / 1000000000000) (17211755103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1354475177921957 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4838228885 / 1000000000000) (4838228886 / 1000000000000), orderedInterval (43081625789 / 1000000000000) (43081625790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1196719896805097 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46053647765 / 1000000000000) (-46053647703 / 1000000000000), orderedInterval (-2557588901 / 1000000000000) (-2557588840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (346856070492603 / 800000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27896286270 / 1000000000000) (27896286271 / 1000000000000), orderedInterval (26237916729 / 1000000000000) (26237916730 / 1000000000000)))) (orderedInterval (15623572197 / 1000000000000) (15623572325 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate363_chunkChecks4_2 :
    compactCertificate363.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (959422145017441 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49085306567 / 1000000000000) (49085310630 / 1000000000000), orderedInterval (-15748658912 / 1000000000000) (-15748654849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (813312777640601 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (5059527060 / 1000000000000) (5059527072 / 1000000000000), orderedInterval (-55738616359 / 1000000000000) (-55738616347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (508933372924403 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50124578607 / 1000000000000) (50124644819 / 1000000000000), orderedInterval (-50107765892 / 1000000000000) (-50107699679 / 1000000000000)))) (orderedInterval (-8571988900 / 1000000000000) (-8571987943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (273706060594701 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9154034910 / 1000000000000) (9154034912 / 1000000000000), orderedInterval (95954713268 / 1000000000000) (95954713270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (743165197927103 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55012856698 / 1000000000000) (-55012856697 / 1000000000000), orderedInterval (-19854644788 / 1000000000000) (-19854644787 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1014728542622431 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (98379594 / 1000000000000) (98379596 / 1000000000000), orderedInterval (-50095231072 / 1000000000000) (-50095231070 / 1000000000000)))) (orderedInterval (523172413 / 1000000000000) (523172441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (429066627075597 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72779391493 / 1000000000000) (72779391494 / 1000000000000), orderedInterval (24920147004 / 1000000000000) (24920147005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1744132017995437 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5208498490 / 1000000000000) (-5208498489 / 1000000000000), orderedInterval (-37847680322 / 1000000000000) (-37847680321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1164999357855683 / 4000000000000) 4 (IntervalRat.scale (469 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6214084163 / 1000000000000) (6214084175 / 1000000000000), orderedInterval (-46348648371 / 1000000000000) (-46348648359 / 1000000000000)))) (orderedInterval (2624183190 / 1000000000000) (2624183531 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate363_chunkChecks4 :
    compactCertificate363.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate363.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate363_chunkChecks4_0
    compactCertificate363_chunkChecks4_1 compactCertificate363_chunkChecks4_2

theorem compactCertificate363_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate363.chunkCheck r b = true :=
  compactCertificate363.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate363_chunkChecks0
    · exact compactCertificate363_chunkChecks1
    · exact compactCertificate363_chunkChecks2
    · exact compactCertificate363_chunkChecks3
    · exact compactCertificate363_chunkChecks4)

theorem compactCertificate363_coefficient0 :
    compactCertificate363.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate363_coefficient1 :
    compactCertificate363.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate363_coefficient2 :
    compactCertificate363.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate363_coefficient3 :
    compactCertificate363.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate363_coefficient4 :
    compactCertificate363.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate363_coefficients : ∀ r : Fin 5,
    compactCertificate363.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate363_coefficient0
  · exact compactCertificate363_coefficient1
  · exact compactCertificate363_coefficient2
  · exact compactCertificate363_coefficient3
  · exact compactCertificate363_coefficient4

theorem compactCertificate363_lower : (1 : ℚ) ≤ compactCertificate363.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate363, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate363_proves {t : ℝ} (ht : t ∈ compactCertificate363.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate363.proves compactCertificate363_states compactCertificate363_chunks
    compactCertificate363_coefficients compactCertificate363_lower ht

end Erdos232
