/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate604 : CompactCertificate where
  left := 475
  right := 476
  center := 951 / 2
  grid := fun i =>
    match i.val with
    | 0 => 151
    | 1 => 112
    | 2 => 180
    | 3 => 33
    | 4 => 87
    | 5 => 237
    | 6 => 175
    | 7 => 300
    | 8 => 221
    | 9 => 339
    | 10 => 195
    | 11 => 347
    | 12 => 324
    | 13 => 231
    | 14 => 262
    | 15 => 219
    | 16 => 193
    | 17 => 280
    | 18 => 155
    | 19 => 131
    | 20 => 82
    | 21 => 44
    | 22 => 120
    | 23 => 164
    | 24 => 69
    | 25 => 282
    | _ => 188
  point := fun i =>
    match i.val with
    | 0 => 951 / 2
    | 1 => 1401004591453851 / 4000000000000
    | 2 => 453056099420283 / 800000000000
    | 3 => 408809645631057 / 4000000000000
    | 4 => 1098120211998429 / 4000000000000
    | 5 => 2981609990378793 / 4000000000000
    | 6 => 2196240423997809 / 4000000000000
    | 7 => 3763295400239157 / 4000000000000
    | 8 => 2772026358952863 / 4000000000000
    | 9 => 4253001293204049 / 4000000000000
    | 10 => 2455471441494921 / 4000000000000
    | 11 => 4357277162340189 / 4000000000000
    | 12 => 4071133536185841 / 4000000000000
    | 13 => 2905352990601153 / 4000000000000
    | 14 => 3294360635995287 / 4000000000000
    | 15 => 2746494443931303 / 4000000000000
    | 16 => 2426611134033363 / 4000000000000
    | 17 => 703326488354937 / 800000000000
    | 18 => 1945438080834939 / 4000000000000
    | 19 => 1649169406260579 / 4000000000000
    | 20 => 1031973641047137 / 4000000000000
    | 21 => 554998856344479 / 4000000000000
    | 22 => 1506929857630437 / 4000000000000
    | 23 => 2057583889198149 / 4000000000000
    | 24 => 870026358952863 / 4000000000000
    | 25 => 3536608846724223 / 4000000000000
    | _ => 2362290808786257 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))
    | 1 => (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))
    | 2 => (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000))
    | 3 => (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))
    | 4 => (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
    | 5 => (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000))
    | 6 => (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))
    | 7 => (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))
    | 8 => (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000))
    | 9 => (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))
    | 10 => (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))
    | 11 => (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000))
    | 12 => (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))
    | 13 => (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))
    | 14 => (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000))
    | 15 => (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))
    | 16 => (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))
    | 17 => (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000))
    | 18 => (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))
    | 19 => (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))
    | 20 => (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000))
    | 21 => (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))
    | 22 => (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))
    | 23 => (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000))
    | 24 => (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))
    | 25 => (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))
    | _ => (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12028166219 / 1000000000000) (-12028158862 / 1000000000000)
      | 1 => orderedInterval (-69864357 / 1000000000000) (-69863083 / 1000000000000)
      | 2 => orderedInterval (963857643 / 1000000000000) (963857755 / 1000000000000)
      | 3 => orderedInterval (-5601462342 / 1000000000000) (-5601453244 / 1000000000000)
      | 4 => orderedInterval (-3188941826 / 1000000000000) (-3188941738 / 1000000000000)
      | 5 => orderedInterval (2061400231 / 1000000000000) (2061400283 / 1000000000000)
      | 6 => orderedInterval (4846499243 / 1000000000000) (4846499373 / 1000000000000)
      | 7 => orderedInterval (-1567129333 / 1000000000000) (-1567129276 / 1000000000000)
      | _ => orderedInterval (-2644440026 / 1000000000000) (-2644438851 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4852164740 / 1000000000000) (4852172036 / 1000000000000)
      | 1 => orderedInterval (368056405 / 1000000000000) (368057363 / 1000000000000)
      | 2 => orderedInterval (-1963078392 / 1000000000000) (-1963078179 / 1000000000000)
      | 3 => orderedInterval (-922641857 / 1000000000000) (-922629323 / 1000000000000)
      | 4 => orderedInterval (-1471826250 / 1000000000000) (-1471826111 / 1000000000000)
      | 5 => orderedInterval (1847151143 / 1000000000000) (1847151218 / 1000000000000)
      | 6 => orderedInterval (6221575427 / 1000000000000) (6221575546 / 1000000000000)
      | 7 => orderedInterval (-3647714173 / 1000000000000) (-3647714121 / 1000000000000)
      | _ => orderedInterval (-7885377007 / 1000000000000) (-7885374883 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11062418948 / 1000000000000) (11062426224 / 1000000000000)
      | 1 => orderedInterval (-4538326310 / 1000000000000) (-4538325245 / 1000000000000)
      | 2 => orderedInterval (-3140154777 / 1000000000000) (-3140154368 / 1000000000000)
      | 3 => orderedInterval (20900404472 / 1000000000000) (20900422447 / 1000000000000)
      | 4 => orderedInterval (8181963363 / 1000000000000) (8181963587 / 1000000000000)
      | 5 => orderedInterval (-3811657131 / 1000000000000) (-3811657020 / 1000000000000)
      | 6 => orderedInterval (-3310939700 / 1000000000000) (-3310939587 / 1000000000000)
      | 7 => orderedInterval (278146407 / 1000000000000) (278146458 / 1000000000000)
      | _ => orderedInterval (160935536 / 1000000000000) (160939418 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-4736425735 / 1000000000000) (-4736418475 / 1000000000000)
      | 1 => orderedInterval (343723650 / 1000000000000) (343725100 / 1000000000000)
      | 2 => orderedInterval (6013512337 / 1000000000000) (6013513131 / 1000000000000)
      | 3 => orderedInterval (11195457053 / 1000000000000) (11195484217 / 1000000000000)
      | 4 => orderedInterval (5135178204 / 1000000000000) (5135178571 / 1000000000000)
      | 5 => orderedInterval (-4987513752 / 1000000000000) (-4987513582 / 1000000000000)
      | 6 => orderedInterval (-6221291606 / 1000000000000) (-6221291497 / 1000000000000)
      | 7 => orderedInterval (3818942178 / 1000000000000) (3818942231 / 1000000000000)
      | _ => orderedInterval (16414197279 / 1000000000000) (16414204411 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9813864682 / 1000000000000) (-9813857404 / 1000000000000)
      | 1 => orderedInterval (12343465121 / 1000000000000) (12343467277 / 1000000000000)
      | 2 => orderedInterval (10947878035 / 1000000000000) (10947879582 / 1000000000000)
      | 3 => orderedInterval (-92605601791 / 1000000000000) (-92605557785 / 1000000000000)
      | 4 => orderedInterval (-22344734070 / 1000000000000) (-22344733455 / 1000000000000)
      | 5 => orderedInterval (7644354460 / 1000000000000) (7644354726 / 1000000000000)
      | 6 => orderedInterval (2655319049 / 1000000000000) (2655319155 / 1000000000000)
      | 7 => orderedInterval (-61527899 / 1000000000000) (-61527844 / 1000000000000)
      | _ => orderedInterval (11902102794 / 1000000000000) (11902115960 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17228246986 / 1000000000000) (-17228227643 / 1000000000000)
    | 1 => orderedInterval (-2601689964 / 1000000000000) (-2601666454 / 1000000000000)
    | 2 => orderedInterval (25782790808 / 1000000000000) (25782821914 / 1000000000000)
    | 3 => orderedInterval (26975779608 / 1000000000000) (26975824107 / 1000000000000)
    | _ => orderedInterval (-79332608983 / 1000000000000) (-79332539788 / 1000000000000)

theorem compactCertificate604_stateChecks0 :
    compactCertificate604.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (951 / 2)) (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1401004591453851 / 4000000000000)) (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (453056099420283 / 800000000000)) (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks1 :
    compactCertificate604.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (408809645631057 / 4000000000000)) (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1098120211998429 / 4000000000000)) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2981609990378793 / 4000000000000)) (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks2 :
    compactCertificate604.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2196240423997809 / 4000000000000)) (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 300 12 (3763295400239157 / 4000000000000)) (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2772026358952863 / 4000000000000)) (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks3 :
    compactCertificate604.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 339 12 (4253001293204049 / 4000000000000)) (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2455471441494921 / 4000000000000)) (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 347 12 (4357277162340189 / 4000000000000)) (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks4 :
    compactCertificate604.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 324 12 (4071133536185841 / 4000000000000)) (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2905352990601153 / 4000000000000)) (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3294360635995287 / 4000000000000)) (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks5 :
    compactCertificate604.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2746494443931303 / 4000000000000)) (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2426611134033363 / 4000000000000)) (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (703326488354937 / 800000000000)) (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks6 :
    compactCertificate604.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1945438080834939 / 4000000000000)) (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1649169406260579 / 4000000000000)) (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1031973641047137 / 4000000000000)) (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks7 :
    compactCertificate604.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (554998856344479 / 4000000000000)) (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1506929857630437 / 4000000000000)) (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2057583889198149 / 4000000000000)) (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_stateChecks8 :
    compactCertificate604.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (870026358952863 / 4000000000000)) (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (3536608846724223 / 4000000000000)) (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2362290808786257 / 4000000000000)) (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_states : ∀ j,
    BesselStateValid (compactCertificate604.point j) (compactCertificate604.state j) :=
  compactCertificate604.statesValid_of_checks3 compactCertificate604_stateChecks0
    compactCertificate604_stateChecks1 compactCertificate604_stateChecks2
    compactCertificate604_stateChecks3 compactCertificate604_stateChecks4
    compactCertificate604_stateChecks5 compactCertificate604_stateChecks6
    compactCertificate604_stateChecks7 compactCertificate604_stateChecks8

theorem compactCertificate604_chunkChecks0_0 :
    compactCertificate604.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (951 / 2) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1401004591453851 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (453056099420283 / 800000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000)))) (orderedInterval (-12028166219 / 1000000000000) (-12028158862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (408809645631057 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2981609990378793 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000)))) (orderedInterval (-69864357 / 1000000000000) (-69863083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2196240423997809 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3763295400239157 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2772026358952863 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000)))) (orderedInterval (963857643 / 1000000000000) (963857755 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks0_1 :
    compactCertificate604.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4253001293204049 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2455471441494921 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4357277162340189 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000)))) (orderedInterval (-5601462342 / 1000000000000) (-5601453244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4071133536185841 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2905352990601153 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3294360635995287 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000)))) (orderedInterval (-3188941826 / 1000000000000) (-3188941738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2746494443931303 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2426611134033363 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (703326488354937 / 800000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000)))) (orderedInterval (2061400231 / 1000000000000) (2061400283 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks0_2 :
    compactCertificate604.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1945438080834939 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1649169406260579 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1031973641047137 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000)))) (orderedInterval (4846499243 / 1000000000000) (4846499373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (554998856344479 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1506929857630437 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2057583889198149 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000)))) (orderedInterval (-1567129333 / 1000000000000) (-1567129276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (870026358952863 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3536608846724223 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2362290808786257 / 4000000000000) 0 (IntervalRat.scale (951 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000)))) (orderedInterval (-2644440026 / 1000000000000) (-2644438851 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks0 :
    compactCertificate604.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate604.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate604_chunkChecks0_0
    compactCertificate604_chunkChecks0_1 compactCertificate604_chunkChecks0_2

theorem compactCertificate604_chunkChecks1_0 :
    compactCertificate604.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (951 / 2) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1401004591453851 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (453056099420283 / 800000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000)))) (orderedInterval (4852164740 / 1000000000000) (4852172036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (408809645631057 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2981609990378793 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000)))) (orderedInterval (368056405 / 1000000000000) (368057363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2196240423997809 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3763295400239157 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2772026358952863 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000)))) (orderedInterval (-1963078392 / 1000000000000) (-1963078179 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks1_1 :
    compactCertificate604.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4253001293204049 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2455471441494921 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4357277162340189 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000)))) (orderedInterval (-922641857 / 1000000000000) (-922629323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4071133536185841 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2905352990601153 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3294360635995287 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000)))) (orderedInterval (-1471826250 / 1000000000000) (-1471826111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2746494443931303 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2426611134033363 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (703326488354937 / 800000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000)))) (orderedInterval (1847151143 / 1000000000000) (1847151218 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks1_2 :
    compactCertificate604.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1945438080834939 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1649169406260579 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1031973641047137 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000)))) (orderedInterval (6221575427 / 1000000000000) (6221575546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (554998856344479 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1506929857630437 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2057583889198149 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000)))) (orderedInterval (-3647714173 / 1000000000000) (-3647714121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (870026358952863 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3536608846724223 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2362290808786257 / 4000000000000) 1 (IntervalRat.scale (951 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000)))) (orderedInterval (-7885377007 / 1000000000000) (-7885374883 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks1 :
    compactCertificate604.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate604.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate604_chunkChecks1_0
    compactCertificate604_chunkChecks1_1 compactCertificate604_chunkChecks1_2

theorem compactCertificate604_chunkChecks2_0 :
    compactCertificate604.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (951 / 2) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1401004591453851 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (453056099420283 / 800000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000)))) (orderedInterval (11062418948 / 1000000000000) (11062426224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (408809645631057 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2981609990378793 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000)))) (orderedInterval (-4538326310 / 1000000000000) (-4538325245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2196240423997809 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3763295400239157 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2772026358952863 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000)))) (orderedInterval (-3140154777 / 1000000000000) (-3140154368 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks2_1 :
    compactCertificate604.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4253001293204049 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2455471441494921 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4357277162340189 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000)))) (orderedInterval (20900404472 / 1000000000000) (20900422447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4071133536185841 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2905352990601153 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3294360635995287 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000)))) (orderedInterval (8181963363 / 1000000000000) (8181963587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2746494443931303 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2426611134033363 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (703326488354937 / 800000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000)))) (orderedInterval (-3811657131 / 1000000000000) (-3811657020 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks2_2 :
    compactCertificate604.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1945438080834939 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1649169406260579 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1031973641047137 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000)))) (orderedInterval (-3310939700 / 1000000000000) (-3310939587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (554998856344479 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1506929857630437 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2057583889198149 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000)))) (orderedInterval (278146407 / 1000000000000) (278146458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (870026358952863 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3536608846724223 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2362290808786257 / 4000000000000) 2 (IntervalRat.scale (951 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000)))) (orderedInterval (160935536 / 1000000000000) (160939418 / 1000000000000))) = true
  rfl'

theorem compactCertificate604_chunkChecks2 :
    compactCertificate604.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate604.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate604_chunkChecks2_0
    compactCertificate604_chunkChecks2_1 compactCertificate604_chunkChecks2_2

theorem compactCertificate604_chunkChecks3_0 :
    compactCertificate604.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (951 / 2) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1401004591453851 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (453056099420283 / 800000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000)))) (orderedInterval (-4736425735 / 1000000000000) (-4736418475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (408809645631057 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2981609990378793 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000)))) (orderedInterval (343723650 / 1000000000000) (343725100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2196240423997809 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3763295400239157 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2772026358952863 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000)))) (orderedInterval (6013512337 / 1000000000000) (6013513131 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate604_chunkChecks3_1 :
    compactCertificate604.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4253001293204049 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2455471441494921 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4357277162340189 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000)))) (orderedInterval (11195457053 / 1000000000000) (11195484217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4071133536185841 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2905352990601153 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3294360635995287 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000)))) (orderedInterval (5135178204 / 1000000000000) (5135178571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2746494443931303 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2426611134033363 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (703326488354937 / 800000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000)))) (orderedInterval (-4987513752 / 1000000000000) (-4987513582 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate604_chunkChecks3_2 :
    compactCertificate604.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1945438080834939 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1649169406260579 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1031973641047137 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000)))) (orderedInterval (-6221291606 / 1000000000000) (-6221291497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (554998856344479 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1506929857630437 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2057583889198149 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000)))) (orderedInterval (3818942178 / 1000000000000) (3818942231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (870026358952863 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3536608846724223 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2362290808786257 / 4000000000000) 3 (IntervalRat.scale (951 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000)))) (orderedInterval (16414197279 / 1000000000000) (16414204411 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate604_chunkChecks3 :
    compactCertificate604.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate604.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate604_chunkChecks3_0
    compactCertificate604_chunkChecks3_1 compactCertificate604_chunkChecks3_2

theorem compactCertificate604_chunkChecks4_0 :
    compactCertificate604.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (951 / 2) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34569994593 / 1000000000000) (-34569977104 / 1000000000000), orderedInterval (12026268146 / 1000000000000) (12026285635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1401004591453851 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31234820900 / 1000000000000) (-31234787665 / 1000000000000), orderedInterval (29061743028 / 1000000000000) (29061776263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (453056099420283 / 800000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33489761747 / 1000000000000) (33489763152 / 1000000000000), orderedInterval (-1632531355 / 1000000000000) (-1632529951 / 1000000000000)))) (orderedInterval (-9813864682 / 1000000000000) (-9813857404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (408809645631057 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49992140258 / 1000000000000) (49992170244 / 1000000000000), orderedInterval (-61316739632 / 1000000000000) (-61316709646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2981609990378793 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29172665722 / 1000000000000) (-29172661346 / 1000000000000), orderedInterval (1756596050 / 1000000000000) (1756600426 / 1000000000000)))) (orderedInterval (12343465121 / 1000000000000) (12343467277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2196240423997809 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2264834411 / 1000000000000) (-2264834410 / 1000000000000), orderedInterval (-33973559920 / 1000000000000) (-33973559919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3763295400239157 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19860134177 / 1000000000000) (-19860131529 / 1000000000000), orderedInterval (16810467950 / 1000000000000) (16810470598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2772026358952863 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14535391750 / 1000000000000) (14535391882 / 1000000000000), orderedInterval (-26606671732 / 1000000000000) (-26606671600 / 1000000000000)))) (orderedInterval (10947878035 / 1000000000000) (10947879582 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate604_chunkChecks4_1 :
    compactCertificate604.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4253001293204049 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20105314243 / 1000000000000) (20105318059 / 1000000000000), orderedInterval (-13956677042 / 1000000000000) (-13956673227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2455471441494921 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28686932777 / 1000000000000) (-28686821668 / 1000000000000), orderedInterval (14656353780 / 1000000000000) (14656464890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4357277162340189 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (678661094 / 1000000000000) (678661096 / 1000000000000), orderedInterval (-24165561147 / 1000000000000) (-24165561146 / 1000000000000)))) (orderedInterval (-92605601791 / 1000000000000) (-92605557785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4071133536185841 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15970605803 / 1000000000000) (15970605804 / 1000000000000), orderedInterval (19238870698 / 1000000000000) (19238870699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2905352990601153 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29249419331 / 1000000000000) (-29249419016 / 1000000000000), orderedInterval (-4556945441 / 1000000000000) (-4556945126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3294360635995287 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26620320647 / 1000000000000) (26620320743 / 1000000000000), orderedInterval (8005040951 / 1000000000000) (8005041046 / 1000000000000)))) (orderedInterval (-22344734070 / 1000000000000) (-22344733455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2746494443931303 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17192195673 / 1000000000000) (17192196185 / 1000000000000), orderedInterval (-25144228625 / 1000000000000) (-25144228112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2426611134033363 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29024161865 / 1000000000000) (-29024161863 / 1000000000000), orderedInterval (-14363401982 / 1000000000000) (-14363401980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (703326488354937 / 800000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7886053359 / 1000000000000) (7886053360 / 1000000000000), orderedInterval (25723604382 / 1000000000000) (25723604383 / 1000000000000)))) (orderedInterval (7644354460 / 1000000000000) (7644354726 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate604_chunkChecks4_2 :
    compactCertificate604.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1945438080834939 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7109711680 / 1000000000000) (-7109711679 / 1000000000000), orderedInterval (-35466647057 / 1000000000000) (-35466647056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1649169406260579 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39260365020 / 1000000000000) (-39260364849 / 1000000000000), orderedInterval (-1601799134 / 1000000000000) (-1601798963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1031973641047137 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45693836115 / 1000000000000) (45693836116 / 1000000000000), orderedInterval (19396095944 / 1000000000000) (19396095945 / 1000000000000)))) (orderedInterval (2655319049 / 1000000000000) (2655319155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (554998856344479 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65342395321 / 1000000000000) (65342395323 / 1000000000000), orderedInterval (17614066352 / 1000000000000) (17614066353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1506929857630437 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20653940336 / 1000000000000) (20653940337 / 1000000000000), orderedInterval (35514975254 / 1000000000000) (35514975255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2057583889198149 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1409190459 / 1000000000000) (-1409190458 / 1000000000000), orderedInterval (35152773897 / 1000000000000) (35152773898 / 1000000000000)))) (orderedInterval (-61527899 / 1000000000000) (-61527844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (870026358952863 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54035080125 / 1000000000000) (-54035080088 / 1000000000000), orderedInterval (-2540594147 / 1000000000000) (-2540594109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3536608846724223 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22457874628 / 1000000000000) (-22457861821 / 1000000000000), orderedInterval (14698681505 / 1000000000000) (14698694313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2362290808786257 / 4000000000000) 4 (IntervalRat.scale (951 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22101398452 / 1000000000000) (22101398453 / 1000000000000), orderedInterval (24260876725 / 1000000000000) (24260876726 / 1000000000000)))) (orderedInterval (11902102794 / 1000000000000) (11902115960 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate604_chunkChecks4 :
    compactCertificate604.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate604.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate604_chunkChecks4_0
    compactCertificate604_chunkChecks4_1 compactCertificate604_chunkChecks4_2

theorem compactCertificate604_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate604.chunkCheck r b = true :=
  compactCertificate604.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate604_chunkChecks0
    · exact compactCertificate604_chunkChecks1
    · exact compactCertificate604_chunkChecks2
    · exact compactCertificate604_chunkChecks3
    · exact compactCertificate604_chunkChecks4)

theorem compactCertificate604_coefficient0 :
    compactCertificate604.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate604_coefficient1 :
    compactCertificate604.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate604_coefficient2 :
    compactCertificate604.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate604_coefficient3 :
    compactCertificate604.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate604_coefficient4 :
    compactCertificate604.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate604_coefficients : ∀ r : Fin 5,
    compactCertificate604.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate604_coefficient0
  · exact compactCertificate604_coefficient1
  · exact compactCertificate604_coefficient2
  · exact compactCertificate604_coefficient3
  · exact compactCertificate604_coefficient4

theorem compactCertificate604_lower : (1 : ℚ) ≤ compactCertificate604.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate604, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate604_proves {t : ℝ} (ht : t ∈ compactCertificate604.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate604.proves compactCertificate604_states compactCertificate604_chunks
    compactCertificate604_coefficients compactCertificate604_lower ht

end Erdos232
