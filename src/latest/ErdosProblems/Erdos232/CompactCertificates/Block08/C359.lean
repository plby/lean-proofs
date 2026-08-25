/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate359 : CompactCertificate where
  left := 230
  right := 231
  center := 461 / 2
  grid := fun i =>
    match i.val with
    | 0 => 73
    | 1 => 54
    | 2 => 87
    | 3 => 16
    | 4 => 42
    | 5 => 115
    | 6 => 85
    | 7 => 145
    | 8 => 107
    | 9 => 164
    | 10 => 95
    | 11 => 168
    | 12 => 157
    | 13 => 112
    | 14 => 127
    | 15 => 106
    | 16 => 94
    | 17 => 136
    | 18 => 75
    | 19 => 64
    | 20 => 40
    | 21 => 21
    | 22 => 58
    | 23 => 79
    | 24 => 34
    | 25 => 136
    | _ => 91
  point := fun i =>
    match i.val with
    | 0 => 461 / 2
    | 1 => 679141026982361 / 4000000000000
    | 2 => 219620254293113 / 800000000000
    | 3 => 198171657871627 / 4000000000000
    | 4 => 532316948192719 / 4000000000000
    | 5 => 1445344064736723 / 4000000000000
    | 6 => 1064633896385899 / 4000000000000
    | 7 => 1824268327560727 / 4000000000000
    | 8 => 1343747793351493 / 4000000000000
    | 9 => 2061654675254539 / 4000000000000
    | 10 => 1190296881734131 / 4000000000000
    | 11 => 2112202704352079 / 4000000000000
    | 12 => 1973493754134251 / 4000000000000
    | 13 => 1408378263582683 / 4000000000000
    | 14 => 1596950844578157 / 4000000000000
    | 15 => 1331371123714333 / 4000000000000
    | 16 => 1176306764236993 / 4000000000000
    | 17 => 340939549034307 / 800000000000
    | 18 => 943056735294329 / 4000000000000
    | 19 => 799439638576369 / 4000000000000
    | 20 => 500252206648507 / 4000000000000
    | 21 => 269037300499269 / 4000000000000
    | 22 => 730488606064807 / 4000000000000
    | 23 => 997419740189639 / 4000000000000
    | 24 => 421747793351493 / 4000000000000
    | 25 => 1714381365236453 / 4000000000000
    | _ => 1145127300578827 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))
    | 1 => (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))
    | 2 => (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000))
    | 3 => (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))
    | 4 => (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))
    | 5 => (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000))
    | 6 => (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))
    | 7 => (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))
    | 8 => (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000))
    | 9 => (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))
    | 10 => (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))
    | 11 => (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000))
    | 12 => (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))
    | 13 => (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))
    | 14 => (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000))
    | 15 => (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))
    | 16 => (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))
    | 17 => (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000))
    | 18 => (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))
    | 19 => (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))
    | 20 => (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000))
    | 21 => (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))
    | 22 => (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))
    | 23 => (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000))
    | 24 => (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))
    | 25 => (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))
    | _ => (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-21485415546 / 1000000000000) (-21485411486 / 1000000000000)
      | 1 => orderedInterval (4519341476 / 1000000000000) (4519341629 / 1000000000000)
      | 2 => orderedInterval (547570008 / 1000000000000) (547570022 / 1000000000000)
      | 3 => orderedInterval (-585583970 / 1000000000000) (-585583877 / 1000000000000)
      | 4 => orderedInterval (4122494308 / 1000000000000) (4122494336 / 1000000000000)
      | 5 => orderedInterval (1156814402 / 1000000000000) (1156814479 / 1000000000000)
      | 6 => orderedInterval (8377290856 / 1000000000000) (8377290977 / 1000000000000)
      | 7 => orderedInterval (3923460141 / 1000000000000) (3923461096 / 1000000000000)
      | _ => orderedInterval (5255649173 / 1000000000000) (5255657461 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9358848776 / 1000000000000) (9358853008 / 1000000000000)
      | 1 => orderedInterval (2361301575 / 1000000000000) (2361301679 / 1000000000000)
      | 2 => orderedInterval (-727761240 / 1000000000000) (-727761216 / 1000000000000)
      | 3 => orderedInterval (-6566554240 / 1000000000000) (-6566554049 / 1000000000000)
      | 4 => orderedInterval (4207675920 / 1000000000000) (4207675965 / 1000000000000)
      | 5 => orderedInterval (-720747250 / 1000000000000) (-720747149 / 1000000000000)
      | 6 => orderedInterval (3772018444 / 1000000000000) (3772018553 / 1000000000000)
      | 7 => orderedInterval (-2215544773 / 1000000000000) (-2215543917 / 1000000000000)
      | _ => orderedInterval (7397667441 / 1000000000000) (7397682718 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (22732417013 / 1000000000000) (22732421469 / 1000000000000)
      | 1 => orderedInterval (-6248814855 / 1000000000000) (-6248814768 / 1000000000000)
      | 2 => orderedInterval (-3159660640 / 1000000000000) (-3159660598 / 1000000000000)
      | 3 => orderedInterval (2945480356 / 1000000000000) (2945480764 / 1000000000000)
      | 4 => orderedInterval (-10921054846 / 1000000000000) (-10921054772 / 1000000000000)
      | 5 => orderedInterval (-1495162627 / 1000000000000) (-1495162489 / 1000000000000)
      | 6 => orderedInterval (-8080518632 / 1000000000000) (-8080518532 / 1000000000000)
      | 7 => orderedInterval (-3545862485 / 1000000000000) (-3545861608 / 1000000000000)
      | _ => orderedInterval (-3376525342 / 1000000000000) (-3376496952 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9919683697 / 1000000000000) (-9919678995 / 1000000000000)
      | 1 => orderedInterval (-7472680923 / 1000000000000) (-7472680833 / 1000000000000)
      | 2 => orderedInterval (555564501 / 1000000000000) (555564577 / 1000000000000)
      | 3 => orderedInterval (16734391254 / 1000000000000) (16734392150 / 1000000000000)
      | 4 => orderedInterval (-11754955358 / 1000000000000) (-11754955232 / 1000000000000)
      | 5 => orderedInterval (-2225855518 / 1000000000000) (-2225855327 / 1000000000000)
      | 6 => orderedInterval (-3726581604 / 1000000000000) (-3726581512 / 1000000000000)
      | 7 => orderedInterval (2122294650 / 1000000000000) (2122295582 / 1000000000000)
      | _ => orderedInterval (-17037669292 / 1000000000000) (-17037616567 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-24330548368 / 1000000000000) (-24330543353 / 1000000000000)
      | 1 => orderedInterval (13721774257 / 1000000000000) (13721774372 / 1000000000000)
      | 2 => orderedInterval (14541884985 / 1000000000000) (14541885126 / 1000000000000)
      | 3 => orderedInterval (-10909877051 / 1000000000000) (-10909875066 / 1000000000000)
      | 4 => orderedInterval (31238907928 / 1000000000000) (31238908147 / 1000000000000)
      | 5 => orderedInterval (964347844 / 1000000000000) (964348115 / 1000000000000)
      | 6 => orderedInterval (8088448150 / 1000000000000) (8088448236 / 1000000000000)
      | 7 => orderedInterval (4420970887 / 1000000000000) (4420971895 / 1000000000000)
      | _ => orderedInterval (-12294070444 / 1000000000000) (-12293972244 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5831620848 / 1000000000000) (5831634637 / 1000000000000)
    | 1 => orderedInterval (16866904653 / 1000000000000) (16866925592 / 1000000000000)
    | 2 => orderedInterval (-11149702058 / 1000000000000) (-11149667486 / 1000000000000)
    | 3 => orderedInterval (-32725175987 / 1000000000000) (-32725116157 / 1000000000000)
    | _ => orderedInterval (25441838188 / 1000000000000) (25441945228 / 1000000000000)

theorem compactCertificate359_stateChecks0 :
    compactCertificate359.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (461 / 2)) (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (679141026982361 / 4000000000000)) (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (219620254293113 / 800000000000)) (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks1 :
    compactCertificate359.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (198171657871627 / 4000000000000)) (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (532316948192719 / 4000000000000)) (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1445344064736723 / 4000000000000)) (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks2 :
    compactCertificate359.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1064633896385899 / 4000000000000)) (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1824268327560727 / 4000000000000)) (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1343747793351493 / 4000000000000)) (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks3 :
    compactCertificate359.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2061654675254539 / 4000000000000)) (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1190296881734131 / 4000000000000)) (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2112202704352079 / 4000000000000)) (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks4 :
    compactCertificate359.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1973493754134251 / 4000000000000)) (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1408378263582683 / 4000000000000)) (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1596950844578157 / 4000000000000)) (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks5 :
    compactCertificate359.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1331371123714333 / 4000000000000)) (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1176306764236993 / 4000000000000)) (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (340939549034307 / 800000000000)) (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks6 :
    compactCertificate359.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (943056735294329 / 4000000000000)) (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (799439638576369 / 4000000000000)) (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (500252206648507 / 4000000000000)) (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks7 :
    compactCertificate359.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (269037300499269 / 4000000000000)) (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730488606064807 / 4000000000000)) (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (997419740189639 / 4000000000000)) (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_stateChecks8 :
    compactCertificate359.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (421747793351493 / 4000000000000)) (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1714381365236453 / 4000000000000)) (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1145127300578827 / 4000000000000)) (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_states : ∀ j,
    BesselStateValid (compactCertificate359.point j) (compactCertificate359.state j) :=
  compactCertificate359.statesValid_of_checks3 compactCertificate359_stateChecks0
    compactCertificate359_stateChecks1 compactCertificate359_stateChecks2
    compactCertificate359_stateChecks3 compactCertificate359_stateChecks4
    compactCertificate359_stateChecks5 compactCertificate359_stateChecks6
    compactCertificate359_stateChecks7 compactCertificate359_stateChecks8

theorem compactCertificate359_chunkChecks0_0 :
    compactCertificate359.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (461 / 2) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (679141026982361 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (219620254293113 / 800000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000)))) (orderedInterval (-21485415546 / 1000000000000) (-21485411486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (198171657871627 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (532316948192719 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1445344064736723 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000)))) (orderedInterval (4519341476 / 1000000000000) (4519341629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1064633896385899 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1824268327560727 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1343747793351493 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000)))) (orderedInterval (547570008 / 1000000000000) (547570022 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks0_1 :
    compactCertificate359.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2061654675254539 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1190296881734131 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2112202704352079 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000)))) (orderedInterval (-585583970 / 1000000000000) (-585583877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1973493754134251 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1408378263582683 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1596950844578157 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000)))) (orderedInterval (4122494308 / 1000000000000) (4122494336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1331371123714333 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1176306764236993 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (340939549034307 / 800000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000)))) (orderedInterval (1156814402 / 1000000000000) (1156814479 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks0_2 :
    compactCertificate359.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (943056735294329 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (799439638576369 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (500252206648507 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000)))) (orderedInterval (8377290856 / 1000000000000) (8377290977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (269037300499269 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (730488606064807 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (997419740189639 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000)))) (orderedInterval (3923460141 / 1000000000000) (3923461096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (421747793351493 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1714381365236453 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1145127300578827 / 4000000000000) 0 (IntervalRat.scale (461 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000)))) (orderedInterval (5255649173 / 1000000000000) (5255657461 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks0 :
    compactCertificate359.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate359.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate359_chunkChecks0_0
    compactCertificate359_chunkChecks0_1 compactCertificate359_chunkChecks0_2

theorem compactCertificate359_chunkChecks1_0 :
    compactCertificate359.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (461 / 2) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (679141026982361 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (219620254293113 / 800000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000)))) (orderedInterval (9358848776 / 1000000000000) (9358853008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (198171657871627 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (532316948192719 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1445344064736723 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000)))) (orderedInterval (2361301575 / 1000000000000) (2361301679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1064633896385899 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1824268327560727 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1343747793351493 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000)))) (orderedInterval (-727761240 / 1000000000000) (-727761216 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks1_1 :
    compactCertificate359.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2061654675254539 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1190296881734131 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2112202704352079 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000)))) (orderedInterval (-6566554240 / 1000000000000) (-6566554049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1973493754134251 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1408378263582683 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1596950844578157 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000)))) (orderedInterval (4207675920 / 1000000000000) (4207675965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1331371123714333 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1176306764236993 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (340939549034307 / 800000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000)))) (orderedInterval (-720747250 / 1000000000000) (-720747149 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks1_2 :
    compactCertificate359.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (943056735294329 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (799439638576369 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (500252206648507 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000)))) (orderedInterval (3772018444 / 1000000000000) (3772018553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (269037300499269 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (730488606064807 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (997419740189639 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000)))) (orderedInterval (-2215544773 / 1000000000000) (-2215543917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (421747793351493 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1714381365236453 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1145127300578827 / 4000000000000) 1 (IntervalRat.scale (461 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000)))) (orderedInterval (7397667441 / 1000000000000) (7397682718 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks1 :
    compactCertificate359.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate359.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate359_chunkChecks1_0
    compactCertificate359_chunkChecks1_1 compactCertificate359_chunkChecks1_2

theorem compactCertificate359_chunkChecks2_0 :
    compactCertificate359.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (461 / 2) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (679141026982361 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (219620254293113 / 800000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000)))) (orderedInterval (22732417013 / 1000000000000) (22732421469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (198171657871627 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (532316948192719 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1445344064736723 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000)))) (orderedInterval (-6248814855 / 1000000000000) (-6248814768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1064633896385899 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1824268327560727 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1343747793351493 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000)))) (orderedInterval (-3159660640 / 1000000000000) (-3159660598 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks2_1 :
    compactCertificate359.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2061654675254539 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1190296881734131 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2112202704352079 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000)))) (orderedInterval (2945480356 / 1000000000000) (2945480764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1973493754134251 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1408378263582683 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1596950844578157 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000)))) (orderedInterval (-10921054846 / 1000000000000) (-10921054772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1331371123714333 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1176306764236993 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (340939549034307 / 800000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000)))) (orderedInterval (-1495162627 / 1000000000000) (-1495162489 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks2_2 :
    compactCertificate359.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (943056735294329 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (799439638576369 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (500252206648507 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000)))) (orderedInterval (-8080518632 / 1000000000000) (-8080518532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (269037300499269 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (730488606064807 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (997419740189639 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000)))) (orderedInterval (-3545862485 / 1000000000000) (-3545861608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (421747793351493 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1714381365236453 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1145127300578827 / 4000000000000) 2 (IntervalRat.scale (461 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000)))) (orderedInterval (-3376525342 / 1000000000000) (-3376496952 / 1000000000000))) = true
  rfl'

theorem compactCertificate359_chunkChecks2 :
    compactCertificate359.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate359.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate359_chunkChecks2_0
    compactCertificate359_chunkChecks2_1 compactCertificate359_chunkChecks2_2

theorem compactCertificate359_chunkChecks3_0 :
    compactCertificate359.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (461 / 2) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (679141026982361 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (219620254293113 / 800000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000)))) (orderedInterval (-9919683697 / 1000000000000) (-9919678995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (198171657871627 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (532316948192719 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1445344064736723 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000)))) (orderedInterval (-7472680923 / 1000000000000) (-7472680833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1064633896385899 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1824268327560727 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1343747793351493 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000)))) (orderedInterval (555564501 / 1000000000000) (555564577 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate359_chunkChecks3_1 :
    compactCertificate359.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2061654675254539 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1190296881734131 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2112202704352079 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000)))) (orderedInterval (16734391254 / 1000000000000) (16734392150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1973493754134251 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1408378263582683 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1596950844578157 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000)))) (orderedInterval (-11754955358 / 1000000000000) (-11754955232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1331371123714333 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1176306764236993 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (340939549034307 / 800000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000)))) (orderedInterval (-2225855518 / 1000000000000) (-2225855327 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate359_chunkChecks3_2 :
    compactCertificate359.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (943056735294329 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (799439638576369 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (500252206648507 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000)))) (orderedInterval (-3726581604 / 1000000000000) (-3726581512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (269037300499269 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (730488606064807 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (997419740189639 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000)))) (orderedInterval (2122294650 / 1000000000000) (2122295582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (421747793351493 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1714381365236453 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1145127300578827 / 4000000000000) 3 (IntervalRat.scale (461 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000)))) (orderedInterval (-17037669292 / 1000000000000) (-17037616567 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate359_chunkChecks3 :
    compactCertificate359.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate359.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate359_chunkChecks3_0
    compactCertificate359_chunkChecks3_1 compactCertificate359_chunkChecks3_2

theorem compactCertificate359_chunkChecks4_0 :
    compactCertificate359.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (461 / 2) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48847702959 / 1000000000000) (-48847695006 / 1000000000000), orderedInterval (19491658307 / 1000000000000) (19491666260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (679141026982361 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48862351201 / 1000000000000) (48862351202 / 1000000000000), orderedInterval (36761726917 / 1000000000000) (36761726918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (219620254293113 / 800000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43952766028 / 1000000000000) (-43952750840 / 1000000000000), orderedInterval (19755822897 / 1000000000000) (19755838085 / 1000000000000)))) (orderedInterval (-24330548368 / 1000000000000) (-24330543353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (198171657871627 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (6831991307 / 1000000000000) (6831991311 / 1000000000000), orderedInterval (113085103667 / 1000000000000) (113085103671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (532316948192719 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65065416325 / 1000000000000) (65065419734 / 1000000000000), orderedInterval (-23701445335 / 1000000000000) (-23701441925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1445344064736723 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31197397636 / 1000000000000) (-31197397635 / 1000000000000), orderedInterval (-28038354056 / 1000000000000) (-28038354055 / 1000000000000)))) (orderedInterval (13721774257 / 1000000000000) (13721774372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1064633896385899 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4491766028 / 1000000000000) (4491766035 / 1000000000000), orderedInterval (-48708649582 / 1000000000000) (-48708649574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1824268327560727 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36204512146 / 1000000000000) (-36204512134 / 1000000000000), orderedInterval (-9186531866 / 1000000000000) (-9186531855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1343747793351493 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23548550042 / 1000000000000) (-23548550041 / 1000000000000), orderedInterval (-36578117768 / 1000000000000) (-36578117767 / 1000000000000)))) (orderedInterval (14541884985 / 1000000000000) (14541885126 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate359_chunkChecks4_1 :
    compactCertificate359.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2061654675254539 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29141232985 / 1000000000000) (29141232986 / 1000000000000), orderedInterval (19617368142 / 1000000000000) (19617368143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1190296881734131 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4254066718 / 1000000000000) (4254066724 / 1000000000000), orderedInterval (-46064400849 / 1000000000000) (-46064400843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2112202704352079 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30088587458 / 1000000000000) (30088587459 / 1000000000000), orderedInterval (17300104315 / 1000000000000) (17300104317 / 1000000000000)))) (orderedInterval (-10909877051 / 1000000000000) (-10909875066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1973493754134251 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28763777257 / 1000000000000) (-28763777256 / 1000000000000), orderedInterval (-21487948194 / 1000000000000) (-21487948193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1408378263582683 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36260431507 / 1000000000000) (36260431508 / 1000000000000), orderedInterval (22158267377 / 1000000000000) (22158267378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1596950844578157 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34448460306 / 1000000000000) (-34448460305 / 1000000000000), orderedInterval (-20153174882 / 1000000000000) (-20153174881 / 1000000000000)))) (orderedInterval (31238907928 / 1000000000000) (31238908147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1331371123714333 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25374814026 / 1000000000000) (25374814027 / 1000000000000), orderedInterval (35582011413 / 1000000000000) (35582011414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1176306764236993 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20155913670 / 1000000000000) (-20155912760 / 1000000000000), orderedInterval (41969335645 / 1000000000000) (41969336555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (340939549034307 / 800000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11313155745 / 1000000000000) (-11313155695 / 1000000000000), orderedInterval (36970197756 / 1000000000000) (36970197806 / 1000000000000)))) (orderedInterval (964347844 / 1000000000000) (964348115 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate359_chunkChecks4_2 :
    compactCertificate359.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (943056735294329 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41642851705 / 1000000000000) (-41642851704 / 1000000000000), orderedInterval (-30994007426 / 1000000000000) (-30994007425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (799439638576369 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-22871510454 / 1000000000000) (-22871509343 / 1000000000000), orderedInterval (51654027509 / 1000000000000) (51654028620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (500252206648507 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13035898600 / 1000000000000) (13035898602 / 1000000000000), orderedInterval (70094115271 / 1000000000000) (70094115272 / 1000000000000)))) (orderedInterval (8088448150 / 1000000000000) (8088448236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (269037300499269 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-85442116575 / 1000000000000) (-85442104789 / 1000000000000), orderedInterval (47160995355 / 1000000000000) (47161007141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (730488606064807 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54910947179 / 1000000000000) (54910947180 / 1000000000000), orderedInterval (21546955702 / 1000000000000) (21546955703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (997419740189639 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-46862897161 / 1000000000000) (-46862887913 / 1000000000000), orderedInterval (18986613900 / 1000000000000) (18986623147 / 1000000000000)))) (orderedInterval (4420970887 / 1000000000000) (4420971895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (421747793351493 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43424077766 / 1000000000000) (-43424065540 / 1000000000000), orderedInterval (64644214265 / 1000000000000) (64644226491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1714381365236453 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32794976522 / 1000000000000) (32795076634 / 1000000000000), orderedInterval (-20283033720 / 1000000000000) (-20282933607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1145127300578827 / 4000000000000) 4 (IntervalRat.scale (461 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43634561889 / 1000000000000) (-43634561888 / 1000000000000), orderedInterval (-17806032648 / 1000000000000) (-17806032647 / 1000000000000)))) (orderedInterval (-12294070444 / 1000000000000) (-12293972244 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate359_chunkChecks4 :
    compactCertificate359.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate359.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate359_chunkChecks4_0
    compactCertificate359_chunkChecks4_1 compactCertificate359_chunkChecks4_2

theorem compactCertificate359_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate359.chunkCheck r b = true :=
  compactCertificate359.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate359_chunkChecks0
    · exact compactCertificate359_chunkChecks1
    · exact compactCertificate359_chunkChecks2
    · exact compactCertificate359_chunkChecks3
    · exact compactCertificate359_chunkChecks4)

theorem compactCertificate359_coefficient0 :
    compactCertificate359.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate359_coefficient1 :
    compactCertificate359.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate359_coefficient2 :
    compactCertificate359.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate359_coefficient3 :
    compactCertificate359.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate359_coefficient4 :
    compactCertificate359.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate359_coefficients : ∀ r : Fin 5,
    compactCertificate359.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate359_coefficient0
  · exact compactCertificate359_coefficient1
  · exact compactCertificate359_coefficient2
  · exact compactCertificate359_coefficient3
  · exact compactCertificate359_coefficient4

theorem compactCertificate359_lower : (1 : ℚ) ≤ compactCertificate359.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate359, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate359_proves {t : ℝ} (ht : t ∈ compactCertificate359.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate359.proves compactCertificate359_states compactCertificate359_chunks
    compactCertificate359_coefficients compactCertificate359_lower ht

end Erdos232
