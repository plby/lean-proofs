/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate401 : CompactCertificate where
  left := 272
  right := 273
  center := 545 / 2
  grid := fun i =>
    match i.val with
    | 0 => 87
    | 1 => 64
    | 2 => 103
    | 3 => 19
    | 4 => 50
    | 5 => 136
    | 6 => 100
    | 7 => 172
    | 8 => 126
    | 9 => 194
    | 10 => 112
    | 11 => 199
    | 12 => 186
    | 13 => 133
    | 14 => 150
    | 15 => 125
    | 16 => 111
    | 17 => 160
    | 18 => 89
    | 19 => 75
    | 20 => 47
    | 21 => 25
    | 22 => 69
    | 23 => 94
    | 24 => 40
    | 25 => 161
    | _ => 108
  point := fun i =>
    match i.val with
    | 0 => 545 / 2
    | 1 => 160577813321209 / 800000000000
    | 2 => 51927565548697 / 160000000000
    | 3 => 46856205440363 / 800000000000
    | 4 => 125862358683311 / 800000000000
    | 5 => 341740787540787 / 800000000000
    | 6 => 251724717366731 / 800000000000
    | 7 => 431334593718263 / 800000000000
    | 8 => 317719109490917 / 800000000000
    | 9 => 487462819094891 / 800000000000
    | 10 => 281436789824339 / 800000000000
    | 11 => 499414522287151 / 800000000000
    | 12 => 466617829068619 / 800000000000
    | 13 => 333000500500027 / 800000000000
    | 14 => 377587076049933 / 800000000000
    | 15 => 314792738578877 / 800000000000
    | 16 => 278128931240417 / 800000000000
    | 17 => 80612604869283 / 160000000000
    | 18 => 222978707477401 / 800000000000
    | 19 => 189021519750161 / 800000000000
    | 20 => 118280890509083 / 800000000000
    | 21 => 63611856300261 / 800000000000
    | 22 => 172718564123783 / 800000000000
    | 23 => 235832433146791 / 800000000000
    | 24 => 99719109490917 / 800000000000
    | 25 => 405352643841157 / 800000000000
    | _ => 270756780397163 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))
    | 1 => (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))
    | 2 => (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000))
    | 3 => (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))
    | 4 => (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))
    | 5 => (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000))
    | 6 => (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))
    | 7 => (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))
    | 8 => (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000))
    | 9 => (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))
    | 10 => (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))
    | 11 => (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000))
    | 12 => (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))
    | 13 => (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))
    | 14 => (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000))
    | 15 => (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))
    | 16 => (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))
    | 17 => (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000))
    | 18 => (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))
    | 19 => (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))
    | 20 => (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000))
    | 21 => (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))
    | 22 => (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))
    | 23 => (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000))
    | 24 => (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))
    | 25 => (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))
    | _ => (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1688199996 / 1000000000000) (-1688199886 / 1000000000000)
      | 1 => orderedInterval (-156481921 / 1000000000000) (-156481877 / 1000000000000)
      | 2 => orderedInterval (1251757381 / 1000000000000) (1251759031 / 1000000000000)
      | 3 => orderedInterval (-807597074 / 1000000000000) (-807596965 / 1000000000000)
      | 4 => orderedInterval (2621225230 / 1000000000000) (2621227073 / 1000000000000)
      | 5 => orderedInterval (-276652112 / 1000000000000) (-276651228 / 1000000000000)
      | 6 => orderedInterval (425868063 / 1000000000000) (425868134 / 1000000000000)
      | 7 => orderedInterval (580641113 / 1000000000000) (580641154 / 1000000000000)
      | _ => orderedInterval (3266034624 / 1000000000000) (3266034864 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-18248879385 / 1000000000000) (-18248879256 / 1000000000000)
      | 1 => orderedInterval (-2361238523 / 1000000000000) (-2361238483 / 1000000000000)
      | 2 => orderedInterval (-2637142242 / 1000000000000) (-2637139831 / 1000000000000)
      | 3 => orderedInterval (-17531608319 / 1000000000000) (-17531608094 / 1000000000000)
      | 4 => orderedInterval (-5196724316 / 1000000000000) (-5196721498 / 1000000000000)
      | 5 => orderedInterval (2378089292 / 1000000000000) (2378090912 / 1000000000000)
      | 6 => orderedInterval (7462753329 / 1000000000000) (7462753394 / 1000000000000)
      | 7 => orderedInterval (-2836336544 / 1000000000000) (-2836336512 / 1000000000000)
      | _ => orderedInterval (-10484379791 / 1000000000000) (-10484379381 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2929050566 / 1000000000000) (2929050720 / 1000000000000)
      | 1 => orderedInterval (3728832212 / 1000000000000) (3728832264 / 1000000000000)
      | 2 => orderedInterval (-3389197481 / 1000000000000) (-3389193947 / 1000000000000)
      | 3 => orderedInterval (10911948952 / 1000000000000) (10911949434 / 1000000000000)
      | 4 => orderedInterval (-6342289257 / 1000000000000) (-6342284935 / 1000000000000)
      | 5 => orderedInterval (-854447611 / 1000000000000) (-854444629 / 1000000000000)
      | 6 => orderedInterval (-949706351 / 1000000000000) (-949706288 / 1000000000000)
      | 7 => orderedInterval (1034178303 / 1000000000000) (1034178334 / 1000000000000)
      | _ => orderedInterval (-10623252760 / 1000000000000) (-10623252040 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18166652788 / 1000000000000) (18166652970 / 1000000000000)
      | 1 => orderedInterval (7795248140 / 1000000000000) (7795248218 / 1000000000000)
      | 2 => orderedInterval (9073374752 / 1000000000000) (9073379925 / 1000000000000)
      | 3 => orderedInterval (100339939522 / 1000000000000) (100339940577 / 1000000000000)
      | 4 => orderedInterval (14917353572 / 1000000000000) (14917360190 / 1000000000000)
      | 5 => orderedInterval (-2726243966 / 1000000000000) (-2726238477 / 1000000000000)
      | 6 => orderedInterval (-8191775617 / 1000000000000) (-8191775557 / 1000000000000)
      | 7 => orderedInterval (3742169926 / 1000000000000) (3742169957 / 1000000000000)
      | _ => orderedInterval (17592852041 / 1000000000000) (17592853330 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4569975571 / 1000000000000) (-4569975354 / 1000000000000)
      | 1 => orderedInterval (-10569823890 / 1000000000000) (-10569823770 / 1000000000000)
      | 2 => orderedInterval (10049958923 / 1000000000000) (10049966526 / 1000000000000)
      | 3 => orderedInterval (-65826305466 / 1000000000000) (-65826303122 / 1000000000000)
      | 4 => orderedInterval (16052607350 / 1000000000000) (16052617516 / 1000000000000)
      | 5 => orderedInterval (6110320015 / 1000000000000) (6110330153 / 1000000000000)
      | 6 => orderedInterval (773031752 / 1000000000000) (773031812 / 1000000000000)
      | 7 => orderedInterval (-1339123767 / 1000000000000) (-1339123734 / 1000000000000)
      | _ => orderedInterval (35334382268 / 1000000000000) (35334384606 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5216595308 / 1000000000000) (5216600300 / 1000000000000)
    | 1 => orderedInterval (-49455466499 / 1000000000000) (-49455458749 / 1000000000000)
    | 2 => orderedInterval (-3554883427 / 1000000000000) (-3554871087 / 1000000000000)
    | 3 => orderedInterval (160709571158 / 1000000000000) (160709591133 / 1000000000000)
    | _ => orderedInterval (-13984928386 / 1000000000000) (-13984895367 / 1000000000000)

theorem compactCertificate401_stateChecks0 :
    compactCertificate401.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (545 / 2)) (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (160577813321209 / 800000000000)) (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (51927565548697 / 160000000000)) (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks1 :
    compactCertificate401.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (46856205440363 / 800000000000)) (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125862358683311 / 800000000000)) (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (341740787540787 / 800000000000)) (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks2 :
    compactCertificate401.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (251724717366731 / 800000000000)) (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (431334593718263 / 800000000000)) (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (317719109490917 / 800000000000)) (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks3 :
    compactCertificate401.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (487462819094891 / 800000000000)) (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (281436789824339 / 800000000000)) (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (499414522287151 / 800000000000)) (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks4 :
    compactCertificate401.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (466617829068619 / 800000000000)) (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (333000500500027 / 800000000000)) (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (377587076049933 / 800000000000)) (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks5 :
    compactCertificate401.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (314792738578877 / 800000000000)) (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (278128931240417 / 800000000000)) (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (80612604869283 / 160000000000)) (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks6 :
    compactCertificate401.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222978707477401 / 800000000000)) (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (189021519750161 / 800000000000)) (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (118280890509083 / 800000000000)) (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks7 :
    compactCertificate401.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (63611856300261 / 800000000000)) (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (172718564123783 / 800000000000)) (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (235832433146791 / 800000000000)) (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_stateChecks8 :
    compactCertificate401.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (99719109490917 / 800000000000)) (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (405352643841157 / 800000000000)) (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (270756780397163 / 800000000000)) (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_states : ∀ j,
    BesselStateValid (compactCertificate401.point j) (compactCertificate401.state j) :=
  compactCertificate401.statesValid_of_checks3 compactCertificate401_stateChecks0
    compactCertificate401_stateChecks1 compactCertificate401_stateChecks2
    compactCertificate401_stateChecks3 compactCertificate401_stateChecks4
    compactCertificate401_stateChecks5 compactCertificate401_stateChecks6
    compactCertificate401_stateChecks7 compactCertificate401_stateChecks8

theorem compactCertificate401_chunkChecks0_0 :
    compactCertificate401.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (545 / 2) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (160577813321209 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (51927565548697 / 160000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000)))) (orderedInterval (-1688199996 / 1000000000000) (-1688199886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (46856205440363 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (125862358683311 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (341740787540787 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000)))) (orderedInterval (-156481921 / 1000000000000) (-156481877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (251724717366731 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (431334593718263 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (317719109490917 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000)))) (orderedInterval (1251757381 / 1000000000000) (1251759031 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks0_1 :
    compactCertificate401.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (487462819094891 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (281436789824339 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (499414522287151 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000)))) (orderedInterval (-807597074 / 1000000000000) (-807596965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (466617829068619 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (333000500500027 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (377587076049933 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000)))) (orderedInterval (2621225230 / 1000000000000) (2621227073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (314792738578877 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (278128931240417 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (80612604869283 / 160000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000)))) (orderedInterval (-276652112 / 1000000000000) (-276651228 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks0_2 :
    compactCertificate401.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (222978707477401 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (189021519750161 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (118280890509083 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000)))) (orderedInterval (425868063 / 1000000000000) (425868134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (63611856300261 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (172718564123783 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (235832433146791 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000)))) (orderedInterval (580641113 / 1000000000000) (580641154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (99719109490917 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (405352643841157 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (270756780397163 / 800000000000) 0 (IntervalRat.scale (545 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000)))) (orderedInterval (3266034624 / 1000000000000) (3266034864 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks0 :
    compactCertificate401.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate401.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate401_chunkChecks0_0
    compactCertificate401_chunkChecks0_1 compactCertificate401_chunkChecks0_2

theorem compactCertificate401_chunkChecks1_0 :
    compactCertificate401.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (545 / 2) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (160577813321209 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (51927565548697 / 160000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000)))) (orderedInterval (-18248879385 / 1000000000000) (-18248879256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (46856205440363 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (125862358683311 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (341740787540787 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000)))) (orderedInterval (-2361238523 / 1000000000000) (-2361238483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (251724717366731 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (431334593718263 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (317719109490917 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000)))) (orderedInterval (-2637142242 / 1000000000000) (-2637139831 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks1_1 :
    compactCertificate401.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (487462819094891 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (281436789824339 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (499414522287151 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000)))) (orderedInterval (-17531608319 / 1000000000000) (-17531608094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (466617829068619 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (333000500500027 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (377587076049933 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000)))) (orderedInterval (-5196724316 / 1000000000000) (-5196721498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (314792738578877 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (278128931240417 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (80612604869283 / 160000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000)))) (orderedInterval (2378089292 / 1000000000000) (2378090912 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks1_2 :
    compactCertificate401.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (222978707477401 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (189021519750161 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (118280890509083 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000)))) (orderedInterval (7462753329 / 1000000000000) (7462753394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (63611856300261 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (172718564123783 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (235832433146791 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000)))) (orderedInterval (-2836336544 / 1000000000000) (-2836336512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (99719109490917 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (405352643841157 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (270756780397163 / 800000000000) 1 (IntervalRat.scale (545 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000)))) (orderedInterval (-10484379791 / 1000000000000) (-10484379381 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks1 :
    compactCertificate401.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate401.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate401_chunkChecks1_0
    compactCertificate401_chunkChecks1_1 compactCertificate401_chunkChecks1_2

theorem compactCertificate401_chunkChecks2_0 :
    compactCertificate401.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (545 / 2) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (160577813321209 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (51927565548697 / 160000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000)))) (orderedInterval (2929050566 / 1000000000000) (2929050720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (46856205440363 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (125862358683311 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (341740787540787 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000)))) (orderedInterval (3728832212 / 1000000000000) (3728832264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (251724717366731 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (431334593718263 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (317719109490917 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000)))) (orderedInterval (-3389197481 / 1000000000000) (-3389193947 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks2_1 :
    compactCertificate401.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (487462819094891 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (281436789824339 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (499414522287151 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000)))) (orderedInterval (10911948952 / 1000000000000) (10911949434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (466617829068619 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (333000500500027 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (377587076049933 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000)))) (orderedInterval (-6342289257 / 1000000000000) (-6342284935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (314792738578877 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (278128931240417 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (80612604869283 / 160000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000)))) (orderedInterval (-854447611 / 1000000000000) (-854444629 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks2_2 :
    compactCertificate401.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (222978707477401 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (189021519750161 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (118280890509083 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000)))) (orderedInterval (-949706351 / 1000000000000) (-949706288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (63611856300261 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (172718564123783 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (235832433146791 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000)))) (orderedInterval (1034178303 / 1000000000000) (1034178334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (99719109490917 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (405352643841157 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (270756780397163 / 800000000000) 2 (IntervalRat.scale (545 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000)))) (orderedInterval (-10623252760 / 1000000000000) (-10623252040 / 1000000000000))) = true
  rfl'

theorem compactCertificate401_chunkChecks2 :
    compactCertificate401.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate401.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate401_chunkChecks2_0
    compactCertificate401_chunkChecks2_1 compactCertificate401_chunkChecks2_2

theorem compactCertificate401_chunkChecks3_0 :
    compactCertificate401.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (545 / 2) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (160577813321209 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (51927565548697 / 160000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000)))) (orderedInterval (18166652788 / 1000000000000) (18166652970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (46856205440363 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (125862358683311 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (341740787540787 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000)))) (orderedInterval (7795248140 / 1000000000000) (7795248218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (251724717366731 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (431334593718263 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (317719109490917 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000)))) (orderedInterval (9073374752 / 1000000000000) (9073379925 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate401_chunkChecks3_1 :
    compactCertificate401.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (487462819094891 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (281436789824339 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (499414522287151 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000)))) (orderedInterval (100339939522 / 1000000000000) (100339940577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (466617829068619 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (333000500500027 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (377587076049933 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000)))) (orderedInterval (14917353572 / 1000000000000) (14917360190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (314792738578877 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (278128931240417 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (80612604869283 / 160000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000)))) (orderedInterval (-2726243966 / 1000000000000) (-2726238477 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate401_chunkChecks3_2 :
    compactCertificate401.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (222978707477401 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (189021519750161 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (118280890509083 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000)))) (orderedInterval (-8191775617 / 1000000000000) (-8191775557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (63611856300261 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (172718564123783 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (235832433146791 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000)))) (orderedInterval (3742169926 / 1000000000000) (3742169957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (99719109490917 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (405352643841157 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (270756780397163 / 800000000000) 3 (IntervalRat.scale (545 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000)))) (orderedInterval (17592852041 / 1000000000000) (17592853330 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate401_chunkChecks3 :
    compactCertificate401.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate401.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate401_chunkChecks3_0
    compactCertificate401_chunkChecks3_1 compactCertificate401_chunkChecks3_2

theorem compactCertificate401_chunkChecks4_0 :
    compactCertificate401.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (545 / 2) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1624765009 / 1000000000000) (1624765012 / 1000000000000), orderedInterval (-48310158841 / 1000000000000) (-48310158838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (160577813321209 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24247919047 / 1000000000000) (24247919048 / 1000000000000), orderedInterval (50769605674 / 1000000000000) (50769605675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (51927565548697 / 160000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43593964307 / 1000000000000) (-43593962782 / 1000000000000), orderedInterval (7885512019 / 1000000000000) (7885513544 / 1000000000000)))) (orderedInterval (-4569975571 / 1000000000000) (-4569975354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (46856205440363 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (34446767829 / 1000000000000) (34446768812 / 1000000000000), orderedInterval (-98696609275 / 1000000000000) (-98696608292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (125862358683311 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54629494604 / 1000000000000) (54629494605 / 1000000000000), orderedInterval (32415635206 / 1000000000000) (32415635207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (341740787540787 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25001914367 / 1000000000000) (25001914368 / 1000000000000), orderedInterval (29385069849 / 1000000000000) (29385069850 / 1000000000000)))) (orderedInterval (-10569823890 / 1000000000000) (-10569823770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (251724717366731 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43112784412 / 1000000000000) (43112784415 / 1000000000000), orderedInterval (12757675933 / 1000000000000) (12757675935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (431334593718263 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13397881394 / 1000000000000) (-13397881296 / 1000000000000), orderedInterval (31654822099 / 1000000000000) (31654822197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (317719109490917 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34695141840 / 1000000000000) (34695209338 / 1000000000000), orderedInterval (-20024182870 / 1000000000000) (-20024115372 / 1000000000000)))) (orderedInterval (10049958923 / 1000000000000) (10049966526 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate401_chunkChecks4_1 :
    compactCertificate401.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (487462819094891 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19425989933 / 1000000000000) (19425989934 / 1000000000000), orderedInterval (25818533916 / 1000000000000) (25818533917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (281436789824339 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28134770656 / 1000000000000) (28134770657 / 1000000000000), orderedInterval (31867106539 / 1000000000000) (31867106540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (499414522287151 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (3936606848 / 1000000000000) (3936606849 / 1000000000000), orderedInterval (-31693675268 / 1000000000000) (-31693675267 / 1000000000000)))) (orderedInterval (-65826305466 / 1000000000000) (-65826303122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (466617829068619 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9090768920 / 1000000000000) (-9090768909 / 1000000000000), orderedInterval (31769730266 / 1000000000000) (31769730277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (333000500500027 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27947658317 / 1000000000000) (27947677441 / 1000000000000), orderedInterval (-27389427516 / 1000000000000) (-27389408392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (377587076049933 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36695793807 / 1000000000000) (36695794068 / 1000000000000), orderedInterval (1456058101 / 1000000000000) (1456058362 / 1000000000000)))) (orderedInterval (16052607350 / 1000000000000) (16052617516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (314792738578877 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40222066525 / 1000000000000) (-40222066238 / 1000000000000), orderedInterval (297500359 / 1000000000000) (297500645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (278128931240417 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11437945253 / 1000000000000) (11437945314 / 1000000000000), orderedInterval (-41251448597 / 1000000000000) (-41251448536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (80612604869283 / 160000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32900183533 / 1000000000000) (32900216747 / 1000000000000), orderedInterval (-13491495643 / 1000000000000) (-13491462429 / 1000000000000)))) (orderedInterval (6110320015 / 1000000000000) (6110330153 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate401_chunkChecks4_2 :
    compactCertificate401.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (222978707477401 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4457840255 / 1000000000000) (4457840262 / 1000000000000), orderedInterval (-47591472006 / 1000000000000) (-47591471999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (189021519750161 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-51479552088 / 1000000000000) (-51479552075 / 1000000000000), orderedInterval (-6541622709 / 1000000000000) (-6541622696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (118280890509083 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54525650217 / 1000000000000) (-54525650216 / 1000000000000), orderedInterval (-36322602956 / 1000000000000) (-36322602955 / 1000000000000)))) (orderedInterval (773031752 / 1000000000000) (773031812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (63611856300261 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87899909866 / 1000000000000) (-87899909476 / 1000000000000), orderedInterval (17278793047 / 1000000000000) (17278793437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (172718564123783 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4711206984 / 1000000000000) (4711206995 / 1000000000000), orderedInterval (-54108190819 / 1000000000000) (-54108190808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (235832433146791 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12207362657 / 1000000000000) (12207362658 / 1000000000000), orderedInterval (44818445843 / 1000000000000) (44818445844 / 1000000000000)))) (orderedInterval (-1339123767 / 1000000000000) (-1339123734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (99719109490917 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-16321935429 / 1000000000000) (-16321935260 / 1000000000000), orderedInterval (69642300962 / 1000000000000) (69642301130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (405352643841157 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35236731596 / 1000000000000) (-35236729601 / 1000000000000), orderedInterval (3881685084 / 1000000000000) (3881687079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (270756780397163 / 800000000000) 4 (IntervalRat.scale (545 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2644062360 / 1000000000000) (-2644062357 / 1000000000000), orderedInterval (43293853248 / 1000000000000) (43293853251 / 1000000000000)))) (orderedInterval (35334382268 / 1000000000000) (35334384606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate401_chunkChecks4 :
    compactCertificate401.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate401.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate401_chunkChecks4_0
    compactCertificate401_chunkChecks4_1 compactCertificate401_chunkChecks4_2

theorem compactCertificate401_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate401.chunkCheck r b = true :=
  compactCertificate401.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate401_chunkChecks0
    · exact compactCertificate401_chunkChecks1
    · exact compactCertificate401_chunkChecks2
    · exact compactCertificate401_chunkChecks3
    · exact compactCertificate401_chunkChecks4)

theorem compactCertificate401_coefficient0 :
    compactCertificate401.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate401_coefficient1 :
    compactCertificate401.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate401_coefficient2 :
    compactCertificate401.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate401_coefficient3 :
    compactCertificate401.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate401_coefficient4 :
    compactCertificate401.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate401_coefficients : ∀ r : Fin 5,
    compactCertificate401.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate401_coefficient0
  · exact compactCertificate401_coefficient1
  · exact compactCertificate401_coefficient2
  · exact compactCertificate401_coefficient3
  · exact compactCertificate401_coefficient4

theorem compactCertificate401_lower : (1 : ℚ) ≤ compactCertificate401.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate401, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate401_proves {t : ℝ} (ht : t ∈ compactCertificate401.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate401.proves compactCertificate401_states compactCertificate401_chunks
    compactCertificate401_coefficients compactCertificate401_lower ht

end Erdos232
