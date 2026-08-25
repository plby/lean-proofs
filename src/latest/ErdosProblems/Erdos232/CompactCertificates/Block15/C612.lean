/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate612 : CompactCertificate where
  left := 483
  right := 484
  center := 967 / 2
  grid := fun i =>
    match i.val with
    | 0 => 154
    | 1 => 113
    | 2 => 183
    | 3 => 33
    | 4 => 89
    | 5 => 241
    | 6 => 178
    | 7 => 305
    | 8 => 224
    | 9 => 344
    | 10 => 199
    | 11 => 353
    | 12 => 330
    | 13 => 235
    | 14 => 267
    | 15 => 222
    | 16 => 196
    | 17 => 285
    | 18 => 157
    | 19 => 134
    | 20 => 84
    | 21 => 45
    | 22 => 122
    | 23 => 167
    | 24 => 70
    | 25 => 286
    | _ => 191
  point := fun i =>
    match i.val with
    | 0 => 967 / 2
    | 1 => 1424575646620267 / 4000000000000
    | 2 => 460678494363211 / 800000000000
    | 3 => 415687620741569 / 4000000000000
    | 4 => 1116595420612493 / 4000000000000
    | 5 => 3031773775705881 / 4000000000000
    | 6 => 2233190841225953 / 4000000000000
    | 7 => 3826610569959269 / 4000000000000
    | 8 => 2818664026401071 / 4000000000000
    | 9 => 4324555468484033 / 4000000000000
    | 10 => 2496783263854457 / 4000000000000
    | 11 => 4430585716070413 / 4000000000000
    | 12 => 4139627896416097 / 4000000000000
    | 13 => 2954233798014001 / 4000000000000
    | 14 => 3349786261837479 / 4000000000000
    | 15 => 2792702552346551 / 4000000000000
    | 16 => 2467437399169571 / 4000000000000
    | 17 => 715159531271529 / 800000000000
    | 18 => 1978168900281163 / 4000000000000
    | 19 => 1676915684389043 / 4000000000000
    | 20 => 1049335973598929 / 4000000000000
    | 21 => 564336376535343 / 4000000000000
    | 22 => 1532283041355029 / 4000000000000
    | 23 => 2092201494063733 / 4000000000000
    | 24 => 884664026401071 / 4000000000000
    | 25 => 3596110152242191 / 4000000000000
    | _ => 2402034923339969 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))
    | 1 => (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))
    | 2 => (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000))
    | 3 => (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))
    | 4 => (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))
    | 5 => (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000))
    | 6 => (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))
    | 7 => (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))
    | 8 => (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000))
    | 9 => (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))
    | 10 => (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))
    | 11 => (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000))
    | 12 => (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))
    | 13 => (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))
    | 14 => (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000))
    | 15 => (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))
    | 16 => (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))
    | 17 => (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000))
    | 18 => (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))
    | 19 => (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))
    | 20 => (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000))
    | 21 => (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))
    | 22 => (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))
    | 23 => (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000))
    | 24 => (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))
    | 25 => (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))
    | _ => (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4342069060 / 1000000000000) (4342069482 / 1000000000000)
      | 1 => orderedInterval (2220207794 / 1000000000000) (2220208106 / 1000000000000)
      | 2 => orderedInterval (175607069 / 1000000000000) (175607364 / 1000000000000)
      | 3 => orderedInterval (-1800249521 / 1000000000000) (-1800249284 / 1000000000000)
      | 4 => orderedInterval (-2125659414 / 1000000000000) (-2125659191 / 1000000000000)
      | 5 => orderedInterval (-999229902 / 1000000000000) (-999228095 / 1000000000000)
      | 6 => orderedInterval (5643787810 / 1000000000000) (5643810557 / 1000000000000)
      | 7 => orderedInterval (-1854056722 / 1000000000000) (-1854055665 / 1000000000000)
      | _ => orderedInterval (3988526350 / 1000000000000) (3988526621 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13205057794 / 1000000000000) (13205058241 / 1000000000000)
      | 1 => orderedInterval (-970539071 / 1000000000000) (-970538607 / 1000000000000)
      | 2 => orderedInterval (981518493 / 1000000000000) (981518940 / 1000000000000)
      | 3 => orderedInterval (-12995394490 / 1000000000000) (-12995393991 / 1000000000000)
      | 4 => orderedInterval (-2323821325 / 1000000000000) (-2323820879 / 1000000000000)
      | 5 => orderedInterval (-264451205 / 1000000000000) (-264448888 / 1000000000000)
      | 6 => orderedInterval (-3430637373 / 1000000000000) (-3430615343 / 1000000000000)
      | 7 => orderedInterval (1701183186 / 1000000000000) (1701184320 / 1000000000000)
      | _ => orderedInterval (1313422632 / 1000000000000) (1313422915 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3730944257 / 1000000000000) (-3730943763 / 1000000000000)
      | 1 => orderedInterval (-4902298921 / 1000000000000) (-4902298206 / 1000000000000)
      | 2 => orderedInterval (593956374 / 1000000000000) (593957060 / 1000000000000)
      | 3 => orderedInterval (10121108557 / 1000000000000) (10121109634 / 1000000000000)
      | 4 => orderedInterval (4150433438 / 1000000000000) (4150434347 / 1000000000000)
      | 5 => orderedInterval (757482535 / 1000000000000) (757485518 / 1000000000000)
      | 6 => orderedInterval (-6209310259 / 1000000000000) (-6209288587 / 1000000000000)
      | 7 => orderedInterval (2532303998 / 1000000000000) (2532305222 / 1000000000000)
      | _ => orderedInterval (-1755261112 / 1000000000000) (-1755260731 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13297737763 / 1000000000000) (-13297737204 / 1000000000000)
      | 1 => orderedInterval (598331058 / 1000000000000) (598332173 / 1000000000000)
      | 2 => orderedInterval (-4153984554 / 1000000000000) (-4153983487 / 1000000000000)
      | 3 => orderedInterval (56618645550 / 1000000000000) (56618647923 / 1000000000000)
      | 4 => orderedInterval (6382265235 / 1000000000000) (6382267109 / 1000000000000)
      | 5 => orderedInterval (2261981701 / 1000000000000) (2261985546 / 1000000000000)
      | 6 => orderedInterval (3746512947 / 1000000000000) (3746534416 / 1000000000000)
      | 7 => orderedInterval (-1983459074 / 1000000000000) (-1983457753 / 1000000000000)
      | _ => orderedInterval (-181795798 / 1000000000000) (-181795212 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2705185991 / 1000000000000) (2705186635 / 1000000000000)
      | 1 => orderedInterval (12370663416 / 1000000000000) (12370665163 / 1000000000000)
      | 2 => orderedInterval (-5042213174 / 1000000000000) (-5042211484 / 1000000000000)
      | 3 => orderedInterval (-50942277188 / 1000000000000) (-50942271913 / 1000000000000)
      | 4 => orderedInterval (-5889230024 / 1000000000000) (-5889226117 / 1000000000000)
      | 5 => orderedInterval (1518550151 / 1000000000000) (1518555133 / 1000000000000)
      | 6 => orderedInterval (6336648716 / 1000000000000) (6336670164 / 1000000000000)
      | 7 => orderedInterval (-2841048812 / 1000000000000) (-2841047382 / 1000000000000)
      | _ => orderedInterval (-11258907414 / 1000000000000) (-11258906449 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (9591002524 / 1000000000000) (9591029895 / 1000000000000)
    | 1 => orderedInterval (-2783661359 / 1000000000000) (-2783633292 / 1000000000000)
    | 2 => orderedInterval (1557470353 / 1000000000000) (1557500494 / 1000000000000)
    | 3 => orderedInterval (49990759302 / 1000000000000) (49990793511 / 1000000000000)
    | _ => orderedInterval (-53042628338 / 1000000000000) (-53042586250 / 1000000000000)

theorem compactCertificate612_stateChecks0 :
    compactCertificate612.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (967 / 2)) (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1424575646620267 / 4000000000000)) (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (460678494363211 / 800000000000)) (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks1 :
    compactCertificate612.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (415687620741569 / 4000000000000)) (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1116595420612493 / 4000000000000)) (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3031773775705881 / 4000000000000)) (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks2 :
    compactCertificate612.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2233190841225953 / 4000000000000)) (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 305 12 (3826610569959269 / 4000000000000)) (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2818664026401071 / 4000000000000)) (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks3 :
    compactCertificate612.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 344 12 (4324555468484033 / 4000000000000)) (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2496783263854457 / 4000000000000)) (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 353 12 (4430585716070413 / 4000000000000)) (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks4 :
    compactCertificate612.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 330 12 (4139627896416097 / 4000000000000)) (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2954233798014001 / 4000000000000)) (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3349786261837479 / 4000000000000)) (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks5 :
    compactCertificate612.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2792702552346551 / 4000000000000)) (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2467437399169571 / 4000000000000)) (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (715159531271529 / 800000000000)) (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks6 :
    compactCertificate612.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1978168900281163 / 4000000000000)) (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1676915684389043 / 4000000000000)) (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1049335973598929 / 4000000000000)) (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks7 :
    compactCertificate612.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (564336376535343 / 4000000000000)) (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1532283041355029 / 4000000000000)) (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2092201494063733 / 4000000000000)) (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_stateChecks8 :
    compactCertificate612.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (884664026401071 / 4000000000000)) (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (3596110152242191 / 4000000000000)) (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2402034923339969 / 4000000000000)) (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_states : ∀ j,
    BesselStateValid (compactCertificate612.point j) (compactCertificate612.state j) :=
  compactCertificate612.statesValid_of_checks3 compactCertificate612_stateChecks0
    compactCertificate612_stateChecks1 compactCertificate612_stateChecks2
    compactCertificate612_stateChecks3 compactCertificate612_stateChecks4
    compactCertificate612_stateChecks5 compactCertificate612_stateChecks6
    compactCertificate612_stateChecks7 compactCertificate612_stateChecks8

theorem compactCertificate612_chunkChecks0_0 :
    compactCertificate612.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (967 / 2) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1424575646620267 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (460678494363211 / 800000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000)))) (orderedInterval (4342069060 / 1000000000000) (4342069482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (415687620741569 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1116595420612493 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3031773775705881 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000)))) (orderedInterval (2220207794 / 1000000000000) (2220208106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2233190841225953 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3826610569959269 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2818664026401071 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000)))) (orderedInterval (175607069 / 1000000000000) (175607364 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks0_1 :
    compactCertificate612.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4324555468484033 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2496783263854457 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4430585716070413 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000)))) (orderedInterval (-1800249521 / 1000000000000) (-1800249284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4139627896416097 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2954233798014001 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3349786261837479 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000)))) (orderedInterval (-2125659414 / 1000000000000) (-2125659191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2792702552346551 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2467437399169571 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (715159531271529 / 800000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000)))) (orderedInterval (-999229902 / 1000000000000) (-999228095 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks0_2 :
    compactCertificate612.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1978168900281163 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1676915684389043 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1049335973598929 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000)))) (orderedInterval (5643787810 / 1000000000000) (5643810557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (564336376535343 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1532283041355029 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2092201494063733 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000)))) (orderedInterval (-1854056722 / 1000000000000) (-1854055665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (884664026401071 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3596110152242191 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2402034923339969 / 4000000000000) 0 (IntervalRat.scale (967 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000)))) (orderedInterval (3988526350 / 1000000000000) (3988526621 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks0 :
    compactCertificate612.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate612.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate612_chunkChecks0_0
    compactCertificate612_chunkChecks0_1 compactCertificate612_chunkChecks0_2

theorem compactCertificate612_chunkChecks1_0 :
    compactCertificate612.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (967 / 2) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1424575646620267 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (460678494363211 / 800000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000)))) (orderedInterval (13205057794 / 1000000000000) (13205058241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (415687620741569 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1116595420612493 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3031773775705881 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000)))) (orderedInterval (-970539071 / 1000000000000) (-970538607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2233190841225953 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3826610569959269 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2818664026401071 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000)))) (orderedInterval (981518493 / 1000000000000) (981518940 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks1_1 :
    compactCertificate612.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4324555468484033 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2496783263854457 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4430585716070413 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000)))) (orderedInterval (-12995394490 / 1000000000000) (-12995393991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4139627896416097 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2954233798014001 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3349786261837479 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000)))) (orderedInterval (-2323821325 / 1000000000000) (-2323820879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2792702552346551 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2467437399169571 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (715159531271529 / 800000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000)))) (orderedInterval (-264451205 / 1000000000000) (-264448888 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks1_2 :
    compactCertificate612.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1978168900281163 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1676915684389043 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1049335973598929 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000)))) (orderedInterval (-3430637373 / 1000000000000) (-3430615343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (564336376535343 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1532283041355029 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2092201494063733 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000)))) (orderedInterval (1701183186 / 1000000000000) (1701184320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (884664026401071 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3596110152242191 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2402034923339969 / 4000000000000) 1 (IntervalRat.scale (967 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000)))) (orderedInterval (1313422632 / 1000000000000) (1313422915 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks1 :
    compactCertificate612.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate612.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate612_chunkChecks1_0
    compactCertificate612_chunkChecks1_1 compactCertificate612_chunkChecks1_2

theorem compactCertificate612_chunkChecks2_0 :
    compactCertificate612.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (967 / 2) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1424575646620267 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (460678494363211 / 800000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000)))) (orderedInterval (-3730944257 / 1000000000000) (-3730943763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (415687620741569 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1116595420612493 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3031773775705881 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000)))) (orderedInterval (-4902298921 / 1000000000000) (-4902298206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2233190841225953 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3826610569959269 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2818664026401071 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000)))) (orderedInterval (593956374 / 1000000000000) (593957060 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks2_1 :
    compactCertificate612.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4324555468484033 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2496783263854457 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4430585716070413 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000)))) (orderedInterval (10121108557 / 1000000000000) (10121109634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4139627896416097 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2954233798014001 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3349786261837479 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000)))) (orderedInterval (4150433438 / 1000000000000) (4150434347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2792702552346551 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2467437399169571 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (715159531271529 / 800000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000)))) (orderedInterval (757482535 / 1000000000000) (757485518 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks2_2 :
    compactCertificate612.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1978168900281163 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1676915684389043 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1049335973598929 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000)))) (orderedInterval (-6209310259 / 1000000000000) (-6209288587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (564336376535343 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1532283041355029 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2092201494063733 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000)))) (orderedInterval (2532303998 / 1000000000000) (2532305222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (884664026401071 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3596110152242191 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2402034923339969 / 4000000000000) 2 (IntervalRat.scale (967 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000)))) (orderedInterval (-1755261112 / 1000000000000) (-1755260731 / 1000000000000))) = true
  rfl'

theorem compactCertificate612_chunkChecks2 :
    compactCertificate612.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate612.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate612_chunkChecks2_0
    compactCertificate612_chunkChecks2_1 compactCertificate612_chunkChecks2_2

theorem compactCertificate612_chunkChecks3_0 :
    compactCertificate612.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (967 / 2) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1424575646620267 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (460678494363211 / 800000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000)))) (orderedInterval (-13297737763 / 1000000000000) (-13297737204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (415687620741569 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1116595420612493 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3031773775705881 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000)))) (orderedInterval (598331058 / 1000000000000) (598332173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2233190841225953 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3826610569959269 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2818664026401071 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000)))) (orderedInterval (-4153984554 / 1000000000000) (-4153983487 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate612_chunkChecks3_1 :
    compactCertificate612.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4324555468484033 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2496783263854457 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4430585716070413 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000)))) (orderedInterval (56618645550 / 1000000000000) (56618647923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4139627896416097 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2954233798014001 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3349786261837479 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000)))) (orderedInterval (6382265235 / 1000000000000) (6382267109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2792702552346551 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2467437399169571 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (715159531271529 / 800000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000)))) (orderedInterval (2261981701 / 1000000000000) (2261985546 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate612_chunkChecks3_2 :
    compactCertificate612.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1978168900281163 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1676915684389043 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1049335973598929 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000)))) (orderedInterval (3746512947 / 1000000000000) (3746534416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (564336376535343 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1532283041355029 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2092201494063733 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000)))) (orderedInterval (-1983459074 / 1000000000000) (-1983457753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (884664026401071 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3596110152242191 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2402034923339969 / 4000000000000) 3 (IntervalRat.scale (967 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000)))) (orderedInterval (-181795798 / 1000000000000) (-181795212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate612_chunkChecks3 :
    compactCertificate612.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate612.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate612_chunkChecks3_0
    compactCertificate612_chunkChecks3_1 compactCertificate612_chunkChecks3_2

theorem compactCertificate612_chunkChecks4_0 :
    compactCertificate612.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (967 / 2) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16752067111 / 1000000000000) (16752067112 / 1000000000000), orderedInterval (32170546295 / 1000000000000) (32170546296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1424575646620267 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39595858232 / 1000000000000) (-39595845902 / 1000000000000), orderedInterval (14877942636 / 1000000000000) (14877954966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (460678494363211 / 800000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870992333 / 1000000000000) (-32870987688 / 1000000000000), orderedInterval (5031716554 / 1000000000000) (5031721199 / 1000000000000)))) (orderedInterval (2705185991 / 1000000000000) (2705186635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (415687620741569 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67241380588 / 1000000000000) (-67241380587 / 1000000000000), orderedInterval (-39732786419 / 1000000000000) (-39732786418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1116595420612493 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-15567785563 / 1000000000000) (-15567785562 / 1000000000000), orderedInterval (-45118781976 / 1000000000000) (-45118781975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3031773775705881 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28964751747 / 1000000000000) (-28964748179 / 1000000000000), orderedInterval (1005775441 / 1000000000000) (1005779009 / 1000000000000)))) (orderedInterval (12370663416 / 1000000000000) (12370665163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2233190841225953 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4062832457 / 1000000000000) (-4062832455 / 1000000000000), orderedInterval (33526483144 / 1000000000000) (33526483146 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3826610569959269 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17543345053 / 1000000000000) (17543345640 / 1000000000000), orderedInterval (-18922048735 / 1000000000000) (-18922048148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2818664026401071 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29655463940 / 1000000000000) (29655474270 / 1000000000000), orderedInterval (-4918771254 / 1000000000000) (-4918760924 / 1000000000000)))) (orderedInterval (-5042213174 / 1000000000000) (-5042211484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate612_chunkChecks4_1 :
    compactCertificate612.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4324555468484033 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22757037705 / 1000000000000) (22757037949 / 1000000000000), orderedInterval (8413191598 / 1000000000000) (8413191843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2496783263854457 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6217067454 / 1000000000000) (6217067457 / 1000000000000), orderedInterval (-31329927230 / 1000000000000) (-31329927227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4430585716070413 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12540935777 / 1000000000000) (12540935789 / 1000000000000), orderedInterval (-20437864697 / 1000000000000) (-20437864685 / 1000000000000)))) (orderedInterval (-50942277188 / 1000000000000) (-50942271913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4139627896416097 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21305192865 / 1000000000000) (-21305183793 / 1000000000000), orderedInterval (12708153446 / 1000000000000) (12708162517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2954233798014001 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25745709970 / 1000000000000) (-25745709967 / 1000000000000), orderedInterval (-14094071526 / 1000000000000) (-14094071524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3349786261837479 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14957897599 / 1000000000000) (14957897731 / 1000000000000), orderedInterval (-23170382898 / 1000000000000) (-23170382766 / 1000000000000)))) (orderedInterval (-5889230024 / 1000000000000) (-5889226117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2792702552346551 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30167996634 / 1000000000000) (30167997688 / 1000000000000), orderedInterval (1291779390 / 1000000000000) (1291780444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2467437399169571 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30478342395 / 1000000000000) (30478372869 / 1000000000000), orderedInterval (-10178700859 / 1000000000000) (-10178670385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (715159531271529 / 800000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (15488862137 / 1000000000000) (15488862305 / 1000000000000), orderedInterval (-21739704011 / 1000000000000) (-21739703844 / 1000000000000)))) (orderedInterval (1518550151 / 1000000000000) (1518555133 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate612_chunkChecks4_2 :
    compactCertificate612.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1978168900281163 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31019355547 / 1000000000000) (-31019249519 / 1000000000000), orderedInterval (18061656453 / 1000000000000) (18061762481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1676915684389043 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31909211526 / 1000000000000) (-31909129920 / 1000000000000), orderedInterval (22406601326 / 1000000000000) (22406682932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1049335973598929 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34464803986 / 1000000000000) (-34464771601 / 1000000000000), orderedInterval (35264128156 / 1000000000000) (35264160541 / 1000000000000)))) (orderedInterval (6336648716 / 1000000000000) (6336670164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (564336376535343 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32024095598 / 1000000000000) (-32024095597 / 1000000000000), orderedInterval (-58935770861 / 1000000000000) (-58935770860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1532283041355029 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22392954113 / 1000000000000) (22392954114 / 1000000000000), orderedInterval (34036029004 / 1000000000000) (34036029005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2092201494063733 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25279058868 / 1000000000000) (25279071907 / 1000000000000), orderedInterval (-24067835971 / 1000000000000) (-24067822931 / 1000000000000)))) (orderedInterval (-2841048812 / 1000000000000) (-2841047382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (884664026401071 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47868795547 / 1000000000000) (47868814067 / 1000000000000), orderedInterval (-24337205985 / 1000000000000) (-24337187464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3596110152242191 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25760085872 / 1000000000000) (25760086146 / 1000000000000), orderedInterval (6659376028 / 1000000000000) (6659376302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2402034923339969 / 4000000000000) 4 (IntervalRat.scale (967 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30895814679 / 1000000000000) (-30895814667 / 1000000000000), orderedInterval (-10249606162 / 1000000000000) (-10249606150 / 1000000000000)))) (orderedInterval (-11258907414 / 1000000000000) (-11258906449 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate612_chunkChecks4 :
    compactCertificate612.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate612.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate612_chunkChecks4_0
    compactCertificate612_chunkChecks4_1 compactCertificate612_chunkChecks4_2

theorem compactCertificate612_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate612.chunkCheck r b = true :=
  compactCertificate612.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate612_chunkChecks0
    · exact compactCertificate612_chunkChecks1
    · exact compactCertificate612_chunkChecks2
    · exact compactCertificate612_chunkChecks3
    · exact compactCertificate612_chunkChecks4)

theorem compactCertificate612_coefficient0 :
    compactCertificate612.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate612_coefficient1 :
    compactCertificate612.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate612_coefficient2 :
    compactCertificate612.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate612_coefficient3 :
    compactCertificate612.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate612_coefficient4 :
    compactCertificate612.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate612_coefficients : ∀ r : Fin 5,
    compactCertificate612.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate612_coefficient0
  · exact compactCertificate612_coefficient1
  · exact compactCertificate612_coefficient2
  · exact compactCertificate612_coefficient3
  · exact compactCertificate612_coefficient4

theorem compactCertificate612_lower : (1 : ℚ) ≤ compactCertificate612.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate612, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate612_proves {t : ℝ} (ht : t ∈ compactCertificate612.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate612.proves compactCertificate612_states compactCertificate612_chunks
    compactCertificate612_coefficients compactCertificate612_lower ht

end Erdos232
