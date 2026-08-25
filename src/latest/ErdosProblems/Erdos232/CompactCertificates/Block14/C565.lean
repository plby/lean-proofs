/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate565 : CompactCertificate where
  left := 436
  right := 437
  center := 873 / 2
  grid := fun i =>
    match i.val with
    | 0 => 139
    | 1 => 102
    | 2 => 166
    | 3 => 30
    | 4 => 80
    | 5 => 218
    | 6 => 161
    | 7 => 275
    | 8 => 203
    | 9 => 311
    | 10 => 179
    | 11 => 318
    | 12 => 298
    | 13 => 212
    | 14 => 241
    | 15 => 201
    | 16 => 177
    | 17 => 257
    | 18 => 142
    | 19 => 121
    | 20 => 75
    | 21 => 41
    | 22 => 110
    | 23 => 150
    | 24 => 64
    | 25 => 258
    | _ => 173
  point := fun i =>
    match i.val with
    | 0 => 873 / 2
    | 1 => 1286095697517573 / 4000000000000
    | 2 => 415896924073509 / 800000000000
    | 3 => 375279516967311 / 4000000000000
    | 4 => 1008053570004867 / 4000000000000
    | 5 => 2737061536909239 / 4000000000000
    | 6 => 2016107140010607 / 4000000000000
    | 7 => 3454633947853611 / 4000000000000
    | 8 => 2544667730142849 / 4000000000000
    | 9 => 3904174688714127 / 4000000000000
    | 10 => 2254076307492183 / 4000000000000
    | 11 => 3999897962905347 / 4000000000000
    | 12 => 3737223530063343 / 4000000000000
    | 13 => 2667059054463519 / 4000000000000
    | 14 => 3024160710014601 / 4000000000000
    | 15 => 2521229915406969 / 4000000000000
    | 16 => 2227583091494349 / 4000000000000
    | 17 => 645640404136551 / 800000000000
    | 18 => 1785875336034597 / 4000000000000
    | 19 => 1513906300384317 / 4000000000000
    | 20 => 947332269857151 / 4000000000000
    | 21 => 509478445414017 / 4000000000000
    | 22 => 1383333086973051 / 4000000000000
    | 23 => 1888823065478427 / 4000000000000
    | 24 => 798667730142849 / 4000000000000
    | 25 => 3246539982324129 / 4000000000000
    | _ => 2168538250336911 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))
    | 1 => (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))
    | 2 => (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000))
    | 3 => (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))
    | 4 => (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
    | 5 => (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000))
    | 6 => (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))
    | 7 => (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))
    | 8 => (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000))
    | 9 => (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))
    | 10 => (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))
    | 11 => (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000))
    | 12 => (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))
    | 13 => (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))
    | 14 => (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000))
    | 15 => (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))
    | 16 => (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))
    | 17 => (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000))
    | 18 => (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))
    | 19 => (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))
    | 20 => (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000))
    | 21 => (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))
    | 22 => (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))
    | 23 => (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000))
    | 24 => (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))
    | 25 => (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))
    | _ => (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9737119032 / 1000000000000) (-9737117833 / 1000000000000)
      | 1 => orderedInterval (1118876743 / 1000000000000) (1118876796 / 1000000000000)
      | 2 => orderedInterval (949423321 / 1000000000000) (949423492 / 1000000000000)
      | 3 => orderedInterval (304821901 / 1000000000000) (304831260 / 1000000000000)
      | 4 => orderedInterval (3297339057 / 1000000000000) (3297339721 / 1000000000000)
      | 5 => orderedInterval (1753973082 / 1000000000000) (1753973201 / 1000000000000)
      | 6 => orderedInterval (-8817249132 / 1000000000000) (-8817246016 / 1000000000000)
      | 7 => orderedInterval (-4400253872 / 1000000000000) (-4400253183 / 1000000000000)
      | _ => orderedInterval (-5861086524 / 1000000000000) (-5861080383 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10921393553 / 1000000000000) (-10921392150 / 1000000000000)
      | 1 => orderedInterval (-3417809804 / 1000000000000) (-3417809743 / 1000000000000)
      | 2 => orderedInterval (665053562 / 1000000000000) (665053817 / 1000000000000)
      | 3 => orderedInterval (9819604442 / 1000000000000) (9819622612 / 1000000000000)
      | 4 => orderedInterval (-43447109 / 1000000000000) (-43445768 / 1000000000000)
      | 5 => orderedInterval (-1814903309 / 1000000000000) (-1814903150 / 1000000000000)
      | 6 => orderedInterval (-848896346 / 1000000000000) (-848893781 / 1000000000000)
      | 7 => orderedInterval (468286324 / 1000000000000) (468286778 / 1000000000000)
      | _ => orderedInterval (8159822394 / 1000000000000) (8159833574 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10588076465 / 1000000000000) (10588078120 / 1000000000000)
      | 1 => orderedInterval (385381676 / 1000000000000) (385381759 / 1000000000000)
      | 2 => orderedInterval (-2744706831 / 1000000000000) (-2744706445 / 1000000000000)
      | 3 => orderedInterval (-10107993726 / 1000000000000) (-10107956284 / 1000000000000)
      | 4 => orderedInterval (-8610757047 / 1000000000000) (-8610754297 / 1000000000000)
      | 5 => orderedInterval (-2355127790 / 1000000000000) (-2355127574 / 1000000000000)
      | 6 => orderedInterval (7549080551 / 1000000000000) (7549082712 / 1000000000000)
      | 7 => orderedInterval (3833479873 / 1000000000000) (3833480280 / 1000000000000)
      | _ => orderedInterval (12908202897 / 1000000000000) (12908223476 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10178463255 / 1000000000000) (10178465211 / 1000000000000)
      | 1 => orderedInterval (8184907895 / 1000000000000) (8184908019 / 1000000000000)
      | 2 => orderedInterval (-4001167784 / 1000000000000) (-4001167193 / 1000000000000)
      | 3 => orderedInterval (-44676942778 / 1000000000000) (-44676862476 / 1000000000000)
      | 4 => orderedInterval (981688713 / 1000000000000) (981694410 / 1000000000000)
      | 5 => orderedInterval (5332795875 / 1000000000000) (5332796174 / 1000000000000)
      | 6 => orderedInterval (1539900083 / 1000000000000) (1539901925 / 1000000000000)
      | 7 => orderedInterval (-437244558 / 1000000000000) (-437244144 / 1000000000000)
      | _ => orderedInterval (-14993125169 / 1000000000000) (-14993087168 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11622298888 / 1000000000000) (-11622296563 / 1000000000000)
      | 1 => orderedInterval (-2223424316 / 1000000000000) (-2223424126 / 1000000000000)
      | 2 => orderedInterval (8689310824 / 1000000000000) (8689311739 / 1000000000000)
      | 3 => orderedInterval (68047152887 / 1000000000000) (68047329949 / 1000000000000)
      | 4 => orderedInterval (24334512066 / 1000000000000) (24334523985 / 1000000000000)
      | 5 => orderedInterval (2040895744 / 1000000000000) (2040896169 / 1000000000000)
      | 6 => orderedInterval (-7169862195 / 1000000000000) (-7169860606 / 1000000000000)
      | 7 => orderedInterval (-4125981740 / 1000000000000) (-4125981301 / 1000000000000)
      | _ => orderedInterval (-34151499744 / 1000000000000) (-34151429310 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21391274456 / 1000000000000) (-21391252945 / 1000000000000)
    | 1 => orderedInterval (2066316601 / 1000000000000) (2066352189 / 1000000000000)
    | 2 => orderedInterval (11445636068 / 1000000000000) (11445701747 / 1000000000000)
    | 3 => orderedInterval (-37890724468 / 1000000000000) (-37890595242 / 1000000000000)
    | _ => orderedInterval (43818804638 / 1000000000000) (43819069936 / 1000000000000)

theorem compactCertificate565_stateChecks0 :
    compactCertificate565.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (873 / 2)) (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1286095697517573 / 4000000000000)) (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (415896924073509 / 800000000000)) (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks1 :
    compactCertificate565.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (375279516967311 / 4000000000000)) (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1008053570004867 / 4000000000000)) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2737061536909239 / 4000000000000)) (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks2 :
    compactCertificate565.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2016107140010607 / 4000000000000)) (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3454633947853611 / 4000000000000)) (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2544667730142849 / 4000000000000)) (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks3 :
    compactCertificate565.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 311 12 (3904174688714127 / 4000000000000)) (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2254076307492183 / 4000000000000)) (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 318 12 (3999897962905347 / 4000000000000)) (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks4 :
    compactCertificate565.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 298 12 (3737223530063343 / 4000000000000)) (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2667059054463519 / 4000000000000)) (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3024160710014601 / 4000000000000)) (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks5 :
    compactCertificate565.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2521229915406969 / 4000000000000)) (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2227583091494349 / 4000000000000)) (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (645640404136551 / 800000000000)) (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks6 :
    compactCertificate565.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1785875336034597 / 4000000000000)) (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1513906300384317 / 4000000000000)) (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (947332269857151 / 4000000000000)) (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks7 :
    compactCertificate565.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (509478445414017 / 4000000000000)) (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1383333086973051 / 4000000000000)) (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1888823065478427 / 4000000000000)) (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_stateChecks8 :
    compactCertificate565.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (798667730142849 / 4000000000000)) (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (3246539982324129 / 4000000000000)) (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2168538250336911 / 4000000000000)) (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_states : ∀ j,
    BesselStateValid (compactCertificate565.point j) (compactCertificate565.state j) :=
  compactCertificate565.statesValid_of_checks3 compactCertificate565_stateChecks0
    compactCertificate565_stateChecks1 compactCertificate565_stateChecks2
    compactCertificate565_stateChecks3 compactCertificate565_stateChecks4
    compactCertificate565_stateChecks5 compactCertificate565_stateChecks6
    compactCertificate565_stateChecks7 compactCertificate565_stateChecks8

theorem compactCertificate565_chunkChecks0_0 :
    compactCertificate565.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (873 / 2) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1286095697517573 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (415896924073509 / 800000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000)))) (orderedInterval (-9737119032 / 1000000000000) (-9737117833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (375279516967311 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2737061536909239 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000)))) (orderedInterval (1118876743 / 1000000000000) (1118876796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2016107140010607 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3454633947853611 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2544667730142849 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000)))) (orderedInterval (949423321 / 1000000000000) (949423492 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks0_1 :
    compactCertificate565.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3904174688714127 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2254076307492183 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3999897962905347 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000)))) (orderedInterval (304821901 / 1000000000000) (304831260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3737223530063343 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2667059054463519 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3024160710014601 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000)))) (orderedInterval (3297339057 / 1000000000000) (3297339721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2521229915406969 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2227583091494349 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (645640404136551 / 800000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000)))) (orderedInterval (1753973082 / 1000000000000) (1753973201 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks0_2 :
    compactCertificate565.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1785875336034597 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1513906300384317 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (947332269857151 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000)))) (orderedInterval (-8817249132 / 1000000000000) (-8817246016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (509478445414017 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1383333086973051 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1888823065478427 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000)))) (orderedInterval (-4400253872 / 1000000000000) (-4400253183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (798667730142849 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3246539982324129 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2168538250336911 / 4000000000000) 0 (IntervalRat.scale (873 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000)))) (orderedInterval (-5861086524 / 1000000000000) (-5861080383 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks0 :
    compactCertificate565.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate565.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate565_chunkChecks0_0
    compactCertificate565_chunkChecks0_1 compactCertificate565_chunkChecks0_2

theorem compactCertificate565_chunkChecks1_0 :
    compactCertificate565.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (873 / 2) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1286095697517573 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (415896924073509 / 800000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000)))) (orderedInterval (-10921393553 / 1000000000000) (-10921392150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (375279516967311 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2737061536909239 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000)))) (orderedInterval (-3417809804 / 1000000000000) (-3417809743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2016107140010607 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3454633947853611 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2544667730142849 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000)))) (orderedInterval (665053562 / 1000000000000) (665053817 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks1_1 :
    compactCertificate565.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3904174688714127 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2254076307492183 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3999897962905347 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000)))) (orderedInterval (9819604442 / 1000000000000) (9819622612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3737223530063343 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2667059054463519 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3024160710014601 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000)))) (orderedInterval (-43447109 / 1000000000000) (-43445768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2521229915406969 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2227583091494349 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (645640404136551 / 800000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000)))) (orderedInterval (-1814903309 / 1000000000000) (-1814903150 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks1_2 :
    compactCertificate565.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1785875336034597 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1513906300384317 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (947332269857151 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000)))) (orderedInterval (-848896346 / 1000000000000) (-848893781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (509478445414017 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1383333086973051 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1888823065478427 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000)))) (orderedInterval (468286324 / 1000000000000) (468286778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (798667730142849 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3246539982324129 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2168538250336911 / 4000000000000) 1 (IntervalRat.scale (873 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000)))) (orderedInterval (8159822394 / 1000000000000) (8159833574 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks1 :
    compactCertificate565.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate565.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate565_chunkChecks1_0
    compactCertificate565_chunkChecks1_1 compactCertificate565_chunkChecks1_2

theorem compactCertificate565_chunkChecks2_0 :
    compactCertificate565.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (873 / 2) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1286095697517573 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (415896924073509 / 800000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000)))) (orderedInterval (10588076465 / 1000000000000) (10588078120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (375279516967311 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2737061536909239 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000)))) (orderedInterval (385381676 / 1000000000000) (385381759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2016107140010607 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3454633947853611 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2544667730142849 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000)))) (orderedInterval (-2744706831 / 1000000000000) (-2744706445 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks2_1 :
    compactCertificate565.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3904174688714127 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2254076307492183 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3999897962905347 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000)))) (orderedInterval (-10107993726 / 1000000000000) (-10107956284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3737223530063343 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2667059054463519 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3024160710014601 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000)))) (orderedInterval (-8610757047 / 1000000000000) (-8610754297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2521229915406969 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2227583091494349 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (645640404136551 / 800000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000)))) (orderedInterval (-2355127790 / 1000000000000) (-2355127574 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks2_2 :
    compactCertificate565.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1785875336034597 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1513906300384317 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (947332269857151 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000)))) (orderedInterval (7549080551 / 1000000000000) (7549082712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (509478445414017 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1383333086973051 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1888823065478427 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000)))) (orderedInterval (3833479873 / 1000000000000) (3833480280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (798667730142849 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3246539982324129 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2168538250336911 / 4000000000000) 2 (IntervalRat.scale (873 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000)))) (orderedInterval (12908202897 / 1000000000000) (12908223476 / 1000000000000))) = true
  rfl'

theorem compactCertificate565_chunkChecks2 :
    compactCertificate565.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate565.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate565_chunkChecks2_0
    compactCertificate565_chunkChecks2_1 compactCertificate565_chunkChecks2_2

theorem compactCertificate565_chunkChecks3_0 :
    compactCertificate565.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (873 / 2) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1286095697517573 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (415896924073509 / 800000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000)))) (orderedInterval (10178463255 / 1000000000000) (10178465211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (375279516967311 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2737061536909239 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000)))) (orderedInterval (8184907895 / 1000000000000) (8184908019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2016107140010607 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3454633947853611 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2544667730142849 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000)))) (orderedInterval (-4001167784 / 1000000000000) (-4001167193 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate565_chunkChecks3_1 :
    compactCertificate565.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3904174688714127 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2254076307492183 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3999897962905347 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000)))) (orderedInterval (-44676942778 / 1000000000000) (-44676862476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3737223530063343 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2667059054463519 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3024160710014601 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000)))) (orderedInterval (981688713 / 1000000000000) (981694410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2521229915406969 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2227583091494349 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (645640404136551 / 800000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000)))) (orderedInterval (5332795875 / 1000000000000) (5332796174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate565_chunkChecks3_2 :
    compactCertificate565.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1785875336034597 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1513906300384317 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (947332269857151 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000)))) (orderedInterval (1539900083 / 1000000000000) (1539901925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (509478445414017 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1383333086973051 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1888823065478427 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000)))) (orderedInterval (-437244558 / 1000000000000) (-437244144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (798667730142849 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3246539982324129 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2168538250336911 / 4000000000000) 3 (IntervalRat.scale (873 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000)))) (orderedInterval (-14993125169 / 1000000000000) (-14993087168 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate565_chunkChecks3 :
    compactCertificate565.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate565.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate565_chunkChecks3_0
    compactCertificate565_chunkChecks3_1 compactCertificate565_chunkChecks3_2

theorem compactCertificate565_chunkChecks4_0 :
    compactCertificate565.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (873 / 2) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21681113371 / 1000000000000) (-21681113370 / 1000000000000), orderedInterval (-31413902176 / 1000000000000) (-31413902175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1286095697517573 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42566164377 / 1000000000000) (42566169862 / 1000000000000), orderedInterval (-13032572358 / 1000000000000) (-13032566874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (415896924073509 / 800000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26245549086 / 1000000000000) (-26245530058 / 1000000000000), orderedInterval (23171372349 / 1000000000000) (23171391377 / 1000000000000)))) (orderedInterval (-11622298888 / 1000000000000) (-11622296563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (375279516967311 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (28722372128 / 1000000000000) (28722372129 / 1000000000000), orderedInterval (77052187178 / 1000000000000) (77052187179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1008053570004867 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50009955766 / 1000000000000) (50009955789 / 1000000000000), orderedInterval (4914175324 / 1000000000000) (4914175347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2737061536909239 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5562788813 / 1000000000000) (5562788814 / 1000000000000), orderedInterval (29986355366 / 1000000000000) (29986355367 / 1000000000000)))) (orderedInterval (-2223424316 / 1000000000000) (-2223424126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2016107140010607 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29603981628 / 1000000000000) (29604051687 / 1000000000000), orderedInterval (-19693308865 / 1000000000000) (-19693238806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3454633947853611 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13153416975 / 1000000000000) (-13153416974 / 1000000000000), orderedInterval (-23743332176 / 1000000000000) (-23743332175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2544667730142849 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22497464416 / 1000000000000) (22497470449 / 1000000000000), orderedInterval (-22256744734 / 1000000000000) (-22256738701 / 1000000000000)))) (orderedInterval (8689310824 / 1000000000000) (8689311739 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate565_chunkChecks4_1 :
    compactCertificate565.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3904174688714127 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5233245730 / 1000000000000) (5233245731 / 1000000000000), orderedInterval (-24999848466 / 1000000000000) (-24999848465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2254076307492183 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31108206194 / 1000000000000) (-31108162565 / 1000000000000), orderedInterval (12755591335 / 1000000000000) (12755634964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3999897962905347 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899204720 / 1000000000000) (24899246600 / 1000000000000), orderedInterval (-4094685060 / 1000000000000) (-4094643181 / 1000000000000)))) (orderedInterval (68047152887 / 1000000000000) (68047329949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3737223530063343 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23304345135 / 1000000000000) (-23304316089 / 1000000000000), orderedInterval (11772163515 / 1000000000000) (11772192560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2667059054463519 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30876802480 / 1000000000000) (30876803406 / 1000000000000), orderedInterval (1165095049 / 1000000000000) (1165095975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3024160710014601 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8531573287 / 1000000000000) (8531573291 / 1000000000000), orderedInterval (-27741130465 / 1000000000000) (-27741130461 / 1000000000000)))) (orderedInterval (24334512066 / 1000000000000) (24334523985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2521229915406969 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11416647697 / 1000000000000) (11416647728 / 1000000000000), orderedInterval (-29668372268 / 1000000000000) (-29668372237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2227583091494349 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33771261300 / 1000000000000) (-33771259965 / 1000000000000), orderedInterval (1661069125 / 1000000000000) (1661070460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (645640404136551 / 800000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12126236881 / 1000000000000) (-12126236880 / 1000000000000), orderedInterval (-25325809072 / 1000000000000) (-25325809071 / 1000000000000)))) (orderedInterval (2040895744 / 1000000000000) (2040896169 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate565_chunkChecks4_2 :
    compactCertificate565.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1785875336034597 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34432858041 / 1000000000000) (34432858042 / 1000000000000), orderedInterval (15462322089 / 1000000000000) (15462322091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1513906300384317 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31375544036 / 1000000000000) (31375589386 / 1000000000000), orderedInterval (-26454198023 / 1000000000000) (-26454152673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (947332269857151 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47176334080 / 1000000000000) (-47176320595 / 1000000000000), orderedInterval (21604076683 / 1000000000000) (21604090168 / 1000000000000)))) (orderedInterval (-7169862195 / 1000000000000) (-7169860606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (509478445414017 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (42856774635 / 1000000000000) (42856793943 / 1000000000000), orderedInterval (-56395585753 / 1000000000000) (-56395566445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1383333086973051 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37068838994 / 1000000000000) (37068838995 / 1000000000000), orderedInterval (21550313945 / 1000000000000) (21550313946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1888823065478427 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36116427815 / 1000000000000) (36116431473 / 1000000000000), orderedInterval (-6655325600 / 1000000000000) (-6655321941 / 1000000000000)))) (orderedInterval (-4125981740 / 1000000000000) (-4125981301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (798667730142849 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32357905301 / 1000000000000) (-32357896225 / 1000000000000), orderedInterval (46356053551 / 1000000000000) (46356062626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3246539982324129 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26597619107 / 1000000000000) (26597690245 / 1000000000000), orderedInterval (-8787490992 / 1000000000000) (-8787419854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2168538250336911 / 4000000000000) 4 (IntervalRat.scale (873 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18658997894 / 1000000000000) (18658998827 / 1000000000000), orderedInterval (-28759611202 / 1000000000000) (-28759610268 / 1000000000000)))) (orderedInterval (-34151499744 / 1000000000000) (-34151429310 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate565_chunkChecks4 :
    compactCertificate565.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate565.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate565_chunkChecks4_0
    compactCertificate565_chunkChecks4_1 compactCertificate565_chunkChecks4_2

theorem compactCertificate565_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate565.chunkCheck r b = true :=
  compactCertificate565.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate565_chunkChecks0
    · exact compactCertificate565_chunkChecks1
    · exact compactCertificate565_chunkChecks2
    · exact compactCertificate565_chunkChecks3
    · exact compactCertificate565_chunkChecks4)

theorem compactCertificate565_coefficient0 :
    compactCertificate565.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate565_coefficient1 :
    compactCertificate565.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate565_coefficient2 :
    compactCertificate565.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate565_coefficient3 :
    compactCertificate565.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate565_coefficient4 :
    compactCertificate565.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate565_coefficients : ∀ r : Fin 5,
    compactCertificate565.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate565_coefficient0
  · exact compactCertificate565_coefficient1
  · exact compactCertificate565_coefficient2
  · exact compactCertificate565_coefficient3
  · exact compactCertificate565_coefficient4

theorem compactCertificate565_lower : (1 : ℚ) ≤ compactCertificate565.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate565, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate565_proves {t : ℝ} (ht : t ∈ compactCertificate565.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate565.proves compactCertificate565_states compactCertificate565_chunks
    compactCertificate565_coefficients compactCertificate565_lower ht

end Erdos232
