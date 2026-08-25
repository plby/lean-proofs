/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate381 : CompactCertificate where
  left := 252
  right := 253
  center := 505 / 2
  grid := fun i =>
    match i.val with
    | 0 => 80
    | 1 => 59
    | 2 => 96
    | 3 => 17
    | 4 => 46
    | 5 => 126
    | 6 => 93
    | 7 => 159
    | 8 => 117
    | 9 => 180
    | 10 => 104
    | 11 => 184
    | 12 => 172
    | 13 => 123
    | 14 => 139
    | 15 => 116
    | 16 => 103
    | 17 => 149
    | 18 => 82
    | 19 => 70
    | 20 => 44
    | 21 => 23
    | 22 => 64
    | 23 => 87
    | 24 => 37
    | 25 => 150
    | _ => 100
  point := fun i =>
    match i.val with
    | 0 => 505 / 2
    | 1 => 148792285738001 / 800000000000
    | 2 => 48116368077233 / 160000000000
    | 3 => 43417217885107 / 800000000000
    | 4 => 116624754376279 / 800000000000
    | 5 => 316658894877243 / 800000000000
    | 6 => 233249508752659 / 800000000000
    | 7 => 399677008858207 / 800000000000
    | 8 => 294400275766813 / 800000000000
    | 9 => 451685731454899 / 800000000000
    | 10 => 260780878644571 / 800000000000
    | 11 => 462760245422039 / 800000000000
    | 12 => 432370648953491 / 800000000000
    | 13 => 308560096793603 / 800000000000
    | 14 => 349874263128837 / 800000000000
    | 15 => 291688684371253 / 800000000000
    | 16 => 257715798672313 / 800000000000
    | 17 => 74696083410987 / 160000000000
    | 18 => 206613297754289 / 800000000000
    | 19 => 175148380685929 / 800000000000
    | 20 => 109599724233187 / 800000000000
    | 21 => 58943096204829 / 800000000000
    | 22 => 160041972261487 / 800000000000
    | 23 => 218523630713999 / 800000000000
    | 24 => 92400275766813 / 800000000000
    | 25 => 375601991082173 / 800000000000
    | _ => 250884723120307 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))
    | 1 => (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))
    | 2 => (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000))
    | 3 => (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))
    | 4 => (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))
    | 5 => (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000))
    | 6 => (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))
    | 7 => (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))
    | 8 => (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000))
    | 9 => (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))
    | 10 => (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))
    | 11 => (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000))
    | 12 => (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))
    | 13 => (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))
    | 14 => (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000))
    | 15 => (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))
    | 16 => (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))
    | 17 => (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000))
    | 18 => (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))
    | 19 => (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))
    | 20 => (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000))
    | 21 => (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))
    | 22 => (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))
    | 23 => (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000))
    | 24 => (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))
    | 25 => (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))
    | _ => (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17676298274 / 1000000000000) (17676302149 / 1000000000000)
      | 1 => orderedInterval (1329482942 / 1000000000000) (1329483506 / 1000000000000)
      | 2 => orderedInterval (-103411001 / 1000000000000) (-103410986 / 1000000000000)
      | 3 => orderedInterval (5042962192 / 1000000000000) (5042962293 / 1000000000000)
      | 4 => orderedInterval (-557667387 / 1000000000000) (-557667356 / 1000000000000)
      | 5 => orderedInterval (-728748245 / 1000000000000) (-728747777 / 1000000000000)
      | 6 => orderedInterval (-8248765425 / 1000000000000) (-8248765284 / 1000000000000)
      | 7 => orderedInterval (3819323159 / 1000000000000) (3819323996 / 1000000000000)
      | _ => orderedInterval (479238138 / 1000000000000) (479243189 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4395480563 / 1000000000000) (-4395476686 / 1000000000000)
      | 1 => orderedInterval (-3881699247 / 1000000000000) (-3881698905 / 1000000000000)
      | 2 => orderedInterval (903259356 / 1000000000000) (903259381 / 1000000000000)
      | 3 => orderedInterval (-4976846232 / 1000000000000) (-4976846022 / 1000000000000)
      | 4 => orderedInterval (-6641879528 / 1000000000000) (-6641879478 / 1000000000000)
      | 5 => orderedInterval (1404899381 / 1000000000000) (1404899987 / 1000000000000)
      | 6 => orderedInterval (-2546938361 / 1000000000000) (-2546938258 / 1000000000000)
      | 7 => orderedInterval (1962222388 / 1000000000000) (1962222652 / 1000000000000)
      | _ => orderedInterval (-13660706019 / 1000000000000) (-13660696661 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17814492934 / 1000000000000) (-17814489039 / 1000000000000)
      | 1 => orderedInterval (4115653681 / 1000000000000) (4115653908 / 1000000000000)
      | 2 => orderedInterval (-1288622001 / 1000000000000) (-1288621956 / 1000000000000)
      | 3 => orderedInterval (-25891262980 / 1000000000000) (-25891262532 / 1000000000000)
      | 4 => orderedInterval (2286208909 / 1000000000000) (2286208992 / 1000000000000)
      | 5 => orderedInterval (244240165 / 1000000000000) (244240958 / 1000000000000)
      | 6 => orderedInterval (8091057883 / 1000000000000) (8091057966 / 1000000000000)
      | 7 => orderedInterval (-2823468988 / 1000000000000) (-2823468889 / 1000000000000)
      | _ => orderedInterval (-5385487666 / 1000000000000) (-5385470266 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (3097579482 / 1000000000000) (3097583381 / 1000000000000)
      | 1 => orderedInterval (8091233662 / 1000000000000) (8091233838 / 1000000000000)
      | 2 => orderedInterval (-4431529541 / 1000000000000) (-4431529461 / 1000000000000)
      | 3 => orderedInterval (38054167188 / 1000000000000) (38054168174 / 1000000000000)
      | 4 => orderedInterval (17325133598 / 1000000000000) (17325133738 / 1000000000000)
      | 5 => orderedInterval (337040860 / 1000000000000) (337041903 / 1000000000000)
      | 6 => orderedInterval (2685468348 / 1000000000000) (2685468419 / 1000000000000)
      | 7 => orderedInterval (-3147211153 / 1000000000000) (-3147211103 / 1000000000000)
      | _ => orderedInterval (27027289512 / 1000000000000) (27027321817 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17811814658 / 1000000000000) (17811818577 / 1000000000000)
      | 1 => orderedInterval (-11784829782 / 1000000000000) (-11784829612 / 1000000000000)
      | 2 => orderedInterval (8655314998 / 1000000000000) (8655315147 / 1000000000000)
      | 3 => orderedInterval (134293125262 / 1000000000000) (134293127446 / 1000000000000)
      | 4 => orderedInterval (-10004518801 / 1000000000000) (-10004518559 / 1000000000000)
      | 5 => orderedInterval (2548807731 / 1000000000000) (2548809124 / 1000000000000)
      | 6 => orderedInterval (-8391956234 / 1000000000000) (-8391956169 / 1000000000000)
      | 7 => orderedInterval (3095295300 / 1000000000000) (3095295337 / 1000000000000)
      | _ => orderedInterval (24339149398 / 1000000000000) (24339209536 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (18708712647 / 1000000000000) (18708723730 / 1000000000000)
    | 1 => orderedInterval (-31833168825 / 1000000000000) (-31833153990 / 1000000000000)
    | 2 => orderedInterval (-38466173931 / 1000000000000) (-38466150858 / 1000000000000)
    | 3 => orderedInterval (89039171956 / 1000000000000) (89039210706 / 1000000000000)
    | _ => orderedInterval (160562202530 / 1000000000000) (160562270827 / 1000000000000)

theorem compactCertificate381_stateChecks0 :
    compactCertificate381.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (505 / 2)) (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148792285738001 / 800000000000)) (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (48116368077233 / 160000000000)) (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks1 :
    compactCertificate381.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (43417217885107 / 800000000000)) (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116624754376279 / 800000000000)) (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (316658894877243 / 800000000000)) (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks2 :
    compactCertificate381.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (233249508752659 / 800000000000)) (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (399677008858207 / 800000000000)) (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (294400275766813 / 800000000000)) (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks3 :
    compactCertificate381.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (451685731454899 / 800000000000)) (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (260780878644571 / 800000000000)) (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (462760245422039 / 800000000000)) (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks4 :
    compactCertificate381.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (432370648953491 / 800000000000)) (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308560096793603 / 800000000000)) (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (349874263128837 / 800000000000)) (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks5 :
    compactCertificate381.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (291688684371253 / 800000000000)) (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (257715798672313 / 800000000000)) (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (74696083410987 / 160000000000)) (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks6 :
    compactCertificate381.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206613297754289 / 800000000000)) (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175148380685929 / 800000000000)) (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (109599724233187 / 800000000000)) (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks7 :
    compactCertificate381.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (58943096204829 / 800000000000)) (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (160041972261487 / 800000000000)) (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (218523630713999 / 800000000000)) (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_stateChecks8 :
    compactCertificate381.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (92400275766813 / 800000000000)) (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (375601991082173 / 800000000000)) (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (250884723120307 / 800000000000)) (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_states : ∀ j,
    BesselStateValid (compactCertificate381.point j) (compactCertificate381.state j) :=
  compactCertificate381.statesValid_of_checks3 compactCertificate381_stateChecks0
    compactCertificate381_stateChecks1 compactCertificate381_stateChecks2
    compactCertificate381_stateChecks3 compactCertificate381_stateChecks4
    compactCertificate381_stateChecks5 compactCertificate381_stateChecks6
    compactCertificate381_stateChecks7 compactCertificate381_stateChecks8

theorem compactCertificate381_chunkChecks0_0 :
    compactCertificate381.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (505 / 2) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (148792285738001 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (48116368077233 / 160000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000)))) (orderedInterval (17676298274 / 1000000000000) (17676302149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (43417217885107 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (116624754376279 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (316658894877243 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000)))) (orderedInterval (1329482942 / 1000000000000) (1329483506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (233249508752659 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (399677008858207 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (294400275766813 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000)))) (orderedInterval (-103411001 / 1000000000000) (-103410986 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks0_1 :
    compactCertificate381.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (451685731454899 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (260780878644571 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (462760245422039 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000)))) (orderedInterval (5042962192 / 1000000000000) (5042962293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (432370648953491 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (308560096793603 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (349874263128837 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000)))) (orderedInterval (-557667387 / 1000000000000) (-557667356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (291688684371253 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (257715798672313 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (74696083410987 / 160000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000)))) (orderedInterval (-728748245 / 1000000000000) (-728747777 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks0_2 :
    compactCertificate381.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (206613297754289 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (175148380685929 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (109599724233187 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000)))) (orderedInterval (-8248765425 / 1000000000000) (-8248765284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (58943096204829 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (160041972261487 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (218523630713999 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000)))) (orderedInterval (3819323159 / 1000000000000) (3819323996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (92400275766813 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (375601991082173 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (250884723120307 / 800000000000) 0 (IntervalRat.scale (505 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000)))) (orderedInterval (479238138 / 1000000000000) (479243189 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks0 :
    compactCertificate381.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate381.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate381_chunkChecks0_0
    compactCertificate381_chunkChecks0_1 compactCertificate381_chunkChecks0_2

theorem compactCertificate381_chunkChecks1_0 :
    compactCertificate381.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (505 / 2) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (148792285738001 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (48116368077233 / 160000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000)))) (orderedInterval (-4395480563 / 1000000000000) (-4395476686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (43417217885107 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (116624754376279 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (316658894877243 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000)))) (orderedInterval (-3881699247 / 1000000000000) (-3881698905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (233249508752659 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (399677008858207 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (294400275766813 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000)))) (orderedInterval (903259356 / 1000000000000) (903259381 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks1_1 :
    compactCertificate381.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (451685731454899 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (260780878644571 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (462760245422039 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000)))) (orderedInterval (-4976846232 / 1000000000000) (-4976846022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (432370648953491 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (308560096793603 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (349874263128837 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000)))) (orderedInterval (-6641879528 / 1000000000000) (-6641879478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (291688684371253 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (257715798672313 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (74696083410987 / 160000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000)))) (orderedInterval (1404899381 / 1000000000000) (1404899987 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks1_2 :
    compactCertificate381.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (206613297754289 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (175148380685929 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (109599724233187 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000)))) (orderedInterval (-2546938361 / 1000000000000) (-2546938258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (58943096204829 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (160041972261487 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (218523630713999 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000)))) (orderedInterval (1962222388 / 1000000000000) (1962222652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (92400275766813 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (375601991082173 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (250884723120307 / 800000000000) 1 (IntervalRat.scale (505 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000)))) (orderedInterval (-13660706019 / 1000000000000) (-13660696661 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks1 :
    compactCertificate381.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate381.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate381_chunkChecks1_0
    compactCertificate381_chunkChecks1_1 compactCertificate381_chunkChecks1_2

theorem compactCertificate381_chunkChecks2_0 :
    compactCertificate381.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (505 / 2) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (148792285738001 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (48116368077233 / 160000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000)))) (orderedInterval (-17814492934 / 1000000000000) (-17814489039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (43417217885107 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (116624754376279 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (316658894877243 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000)))) (orderedInterval (4115653681 / 1000000000000) (4115653908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (233249508752659 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (399677008858207 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (294400275766813 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000)))) (orderedInterval (-1288622001 / 1000000000000) (-1288621956 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks2_1 :
    compactCertificate381.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (451685731454899 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (260780878644571 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (462760245422039 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000)))) (orderedInterval (-25891262980 / 1000000000000) (-25891262532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (432370648953491 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (308560096793603 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (349874263128837 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000)))) (orderedInterval (2286208909 / 1000000000000) (2286208992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (291688684371253 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (257715798672313 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (74696083410987 / 160000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000)))) (orderedInterval (244240165 / 1000000000000) (244240958 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks2_2 :
    compactCertificate381.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (206613297754289 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (175148380685929 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (109599724233187 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000)))) (orderedInterval (8091057883 / 1000000000000) (8091057966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (58943096204829 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (160041972261487 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (218523630713999 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000)))) (orderedInterval (-2823468988 / 1000000000000) (-2823468889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (92400275766813 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (375601991082173 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (250884723120307 / 800000000000) 2 (IntervalRat.scale (505 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000)))) (orderedInterval (-5385487666 / 1000000000000) (-5385470266 / 1000000000000))) = true
  rfl'

theorem compactCertificate381_chunkChecks2 :
    compactCertificate381.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate381.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate381_chunkChecks2_0
    compactCertificate381_chunkChecks2_1 compactCertificate381_chunkChecks2_2

theorem compactCertificate381_chunkChecks3_0 :
    compactCertificate381.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (505 / 2) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (148792285738001 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (48116368077233 / 160000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000)))) (orderedInterval (3097579482 / 1000000000000) (3097583381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (43417217885107 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (116624754376279 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (316658894877243 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000)))) (orderedInterval (8091233662 / 1000000000000) (8091233838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (233249508752659 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (399677008858207 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (294400275766813 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000)))) (orderedInterval (-4431529541 / 1000000000000) (-4431529461 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate381_chunkChecks3_1 :
    compactCertificate381.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (451685731454899 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (260780878644571 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (462760245422039 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000)))) (orderedInterval (38054167188 / 1000000000000) (38054168174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (432370648953491 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (308560096793603 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (349874263128837 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000)))) (orderedInterval (17325133598 / 1000000000000) (17325133738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (291688684371253 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (257715798672313 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (74696083410987 / 160000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000)))) (orderedInterval (337040860 / 1000000000000) (337041903 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate381_chunkChecks3_2 :
    compactCertificate381.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (206613297754289 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (175148380685929 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (109599724233187 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000)))) (orderedInterval (2685468348 / 1000000000000) (2685468419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (58943096204829 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (160041972261487 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (218523630713999 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000)))) (orderedInterval (-3147211153 / 1000000000000) (-3147211103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (92400275766813 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (375601991082173 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (250884723120307 / 800000000000) 3 (IntervalRat.scale (505 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000)))) (orderedInterval (27027289512 / 1000000000000) (27027321817 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate381_chunkChecks3 :
    compactCertificate381.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate381.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate381_chunkChecks3_0
    compactCertificate381_chunkChecks3_1 compactCertificate381_chunkChecks3_2

theorem compactCertificate381_chunkChecks4_0 :
    compactCertificate381.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (505 / 2) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46504529354 / 1000000000000) (46504539083 / 1000000000000), orderedInterval (-19028596134 / 1000000000000) (-19028586405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (148792285738001 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57850993713 / 1000000000000) (-57850993706 / 1000000000000), orderedInterval (-8568876997 / 1000000000000) (-8568876991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (48116368077233 / 160000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3704940598 / 1000000000000) (-3704940593 / 1000000000000), orderedInterval (45866928090 / 1000000000000) (45866928095 / 1000000000000)))) (orderedInterval (17811814658 / 1000000000000) (17811818577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (43417217885107 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107985289533 / 1000000000000) (-107985289459 / 1000000000000), orderedInterval (9298905291 / 1000000000000) (9298905364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (116624754376279 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58571542662 / 1000000000000) (58571557220 / 1000000000000), orderedInterval (-30800246049 / 1000000000000) (-30800231491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (316658894877243 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27861023517 / 1000000000000) (27861023518 / 1000000000000), orderedInterval (28811044700 / 1000000000000) (28811044701 / 1000000000000)))) (orderedInterval (-11784829782 / 1000000000000) (-11784829612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (233249508752659 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8307642685 / 1000000000000) (-8307642684 / 1000000000000), orderedInterval (-45969085608 / 1000000000000) (-45969085607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (399677008858207 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27242159809 / 1000000000000) (-27242159808 / 1000000000000), orderedInterval (-23040746433 / 1000000000000) (-23040746432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (294400275766813 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39046141344 / 1000000000000) (-39046141342 / 1000000000000), orderedInterval (-14276674132 / 1000000000000) (-14276674131 / 1000000000000)))) (orderedInterval (8655314998 / 1000000000000) (8655315147 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate381_chunkChecks4_1 :
    compactCertificate381.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (451685731454899 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3163023758 / 1000000000000) (-3163023757 / 1000000000000), orderedInterval (33432433717 / 1000000000000) (33432433719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (260780878644571 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1567484031 / 1000000000000) (1567484032 / 1000000000000), orderedInterval (44162172701 / 1000000000000) (44162172702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (462760245422039 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30704273888 / 1000000000000) (30704273892 / 1000000000000), orderedInterval (12535630925 / 1000000000000) (12535630929 / 1000000000000)))) (orderedInterval (134293125262 / 1000000000000) (134293127446 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (432370648953491 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26767523682 / 1000000000000) (26767523683 / 1000000000000), orderedInterval (21455796092 / 1000000000000) (21455796093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (308560096793603 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2813146111 / 1000000000000) (-2813146110 / 1000000000000), orderedInterval (-40525896780 / 1000000000000) (-40525896779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (349874263128837 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37858969920 / 1000000000000) (-37858969855 / 1000000000000), orderedInterval (-4684436068 / 1000000000000) (-4684436003 / 1000000000000)))) (orderedInterval (-10004518801 / 1000000000000) (-10004518559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (291688684371253 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34495666661 / 1000000000000) (34495666662 / 1000000000000), orderedInterval (23533909647 / 1000000000000) (23533909648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (257715798672313 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27054555208 / 1000000000000) (27054562786 / 1000000000000), orderedInterval (-35315825573 / 1000000000000) (-35315817995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (74696083410987 / 160000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16448630700 / 1000000000000) (16448631064 / 1000000000000), orderedInterval (-33079543464 / 1000000000000) (-33079543100 / 1000000000000)))) (orderedInterval (2548807731 / 1000000000000) (2548809124 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate381_chunkChecks4_2 :
    compactCertificate381.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (206613297754289 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (49230406825 / 1000000000000) (49230406840 / 1000000000000), orderedInterval (6333822230 / 1000000000000) (6333822246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (175148380685929 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-10246630588 / 1000000000000) (-10246630539 / 1000000000000), orderedInterval (52964971725 / 1000000000000) (52964971774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (109599724233187 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29400899800 / 1000000000000) (-29400897579 / 1000000000000), orderedInterval (61609153292 / 1000000000000) (61609155513 / 1000000000000)))) (orderedInterval (-8391956234 / 1000000000000) (-8391956169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (58943096204829 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74825902171 / 1000000000000) (-74825858622 / 1000000000000), orderedInterval (55657483750 / 1000000000000) (55657527299 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (160041972261487 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-12568775090 / 1000000000000) (-12568774998 / 1000000000000), orderedInterval (55025039586 / 1000000000000) (55025039678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (218523630713999 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28086385879 / 1000000000000) (-28086385878 / 1000000000000), orderedInterval (-39214062926 / 1000000000000) (-39214062925 / 1000000000000)))) (orderedInterval (3095295300 / 1000000000000) (3095295337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (92400275766813 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3394062050 / 1000000000000) (-3394062047 / 1000000000000), orderedInterval (-74149819264 / 1000000000000) (-74149819261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (375601991082173 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29979888037 / 1000000000000) (-29979826863 / 1000000000000), orderedInterval (21413039835 / 1000000000000) (21413101009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (250884723120307 / 800000000000) 4 (IntervalRat.scale (505 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10343486707 / 1000000000000) (10343486708 / 1000000000000), orderedInterval (43835691358 / 1000000000000) (43835691359 / 1000000000000)))) (orderedInterval (24339149398 / 1000000000000) (24339209536 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate381_chunkChecks4 :
    compactCertificate381.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate381.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate381_chunkChecks4_0
    compactCertificate381_chunkChecks4_1 compactCertificate381_chunkChecks4_2

theorem compactCertificate381_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate381.chunkCheck r b = true :=
  compactCertificate381.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate381_chunkChecks0
    · exact compactCertificate381_chunkChecks1
    · exact compactCertificate381_chunkChecks2
    · exact compactCertificate381_chunkChecks3
    · exact compactCertificate381_chunkChecks4)

theorem compactCertificate381_coefficient0 :
    compactCertificate381.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate381_coefficient1 :
    compactCertificate381.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate381_coefficient2 :
    compactCertificate381.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate381_coefficient3 :
    compactCertificate381.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate381_coefficient4 :
    compactCertificate381.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate381_coefficients : ∀ r : Fin 5,
    compactCertificate381.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate381_coefficient0
  · exact compactCertificate381_coefficient1
  · exact compactCertificate381_coefficient2
  · exact compactCertificate381_coefficient3
  · exact compactCertificate381_coefficient4

theorem compactCertificate381_lower : (1 : ℚ) ≤ compactCertificate381.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate381, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate381_proves {t : ℝ} (ht : t ∈ compactCertificate381.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate381.proves compactCertificate381_states compactCertificate381_chunks
    compactCertificate381_coefficients compactCertificate381_lower ht

end Erdos232
