/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate360 : CompactCertificate where
  left := 231
  right := 232
  center := 463 / 2
  grid := fun i =>
    match i.val with
    | 0 => 74
    | 1 => 54
    | 2 => 88
    | 3 => 16
    | 4 => 43
    | 5 => 116
    | 6 => 85
    | 7 => 146
    | 8 => 107
    | 9 => 165
    | 10 => 95
    | 11 => 169
    | 12 => 158
    | 13 => 113
    | 14 => 128
    | 15 => 106
    | 16 => 94
    | 17 => 136
    | 18 => 75
    | 19 => 64
    | 20 => 40
    | 21 => 22
    | 22 => 58
    | 23 => 80
    | 24 => 34
    | 25 => 137
    | _ => 92
  point := fun i =>
    match i.val with
    | 0 => 463 / 2
    | 1 => 682087408878163 / 4000000000000
    | 2 => 220573053660979 / 800000000000
    | 3 => 199031404760441 / 4000000000000
    | 4 => 534626349269477 / 4000000000000
    | 5 => 1451614537902609 / 4000000000000
    | 6 => 1069252698539417 / 4000000000000
    | 7 => 1832182723775741 / 4000000000000
    | 8 => 1349577501782519 / 4000000000000
    | 9 => 2070598947164537 / 4000000000000
    | 10 => 1195460859529073 / 4000000000000
    | 11 => 2121366273568357 / 4000000000000
    | 12 => 1982055549163033 / 4000000000000
    | 13 => 1414488364509289 / 4000000000000
    | 14 => 1603879047808431 / 4000000000000
    | 15 => 1337147137266239 / 4000000000000
    | 16 => 1181410047379019 / 4000000000000
    | 17 => 342418679398881 / 800000000000
    | 18 => 947148087725107 / 4000000000000
    | 19 => 802907923342427 / 4000000000000
    | 20 => 502422498217481 / 4000000000000
    | 21 => 270204490523127 / 4000000000000
    | 22 => 733657754030381 / 4000000000000
    | 23 => 1001746940797837 / 4000000000000
    | 24 => 423577501782519 / 4000000000000
    | 25 => 1721819028426199 / 4000000000000
    | _ => 1150095314898041 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))
    | 1 => (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))
    | 2 => (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000))
    | 3 => (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))
    | 4 => (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))
    | 5 => (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000))
    | 6 => (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))
    | 7 => (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))
    | 8 => (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000))
    | 9 => (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))
    | 10 => (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))
    | 11 => (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000))
    | 12 => (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))
    | 13 => (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))
    | 14 => (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000))
    | 15 => (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))
    | 16 => (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))
    | 17 => (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000))
    | 18 => (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))
    | 19 => (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))
    | 20 => (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000))
    | 21 => (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))
    | 22 => (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))
    | 23 => (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000))
    | 24 => (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))
    | 25 => (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))
    | _ => (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3303759498 / 1000000000000) (-3303759461 / 1000000000000)
      | 1 => orderedInterval (3185304790 / 1000000000000) (3185306468 / 1000000000000)
      | 2 => orderedInterval (-1122773138 / 1000000000000) (-1122772421 / 1000000000000)
      | 3 => orderedInterval (-3703651299 / 1000000000000) (-3703651207 / 1000000000000)
      | 4 => orderedInterval (2361386040 / 1000000000000) (2361386387 / 1000000000000)
      | 5 => orderedInterval (-525200969 / 1000000000000) (-525200488 / 1000000000000)
      | 6 => orderedInterval (7847428084 / 1000000000000) (7847429508 / 1000000000000)
      | 7 => orderedInterval (446493937 / 1000000000000) (446495654 / 1000000000000)
      | _ => orderedInterval (8077850609 / 1000000000000) (8077853838 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (23724603461 / 1000000000000) (23724603500 / 1000000000000)
      | 1 => orderedInterval (-4880395450 / 1000000000000) (-4880393485 / 1000000000000)
      | 2 => orderedInterval (-1567533900 / 1000000000000) (-1567532851 / 1000000000000)
      | 3 => orderedInterval (1237522611 / 1000000000000) (1237522802 / 1000000000000)
      | 4 => orderedInterval (-6795291408 / 1000000000000) (-6795290876 / 1000000000000)
      | 5 => orderedInterval (-2601323494 / 1000000000000) (-2601322797 / 1000000000000)
      | 6 => orderedInterval (-4724046638 / 1000000000000) (-4724045187 / 1000000000000)
      | 7 => orderedInterval (-4101517218 / 1000000000000) (-4101516595 / 1000000000000)
      | _ => orderedInterval (-4187799884 / 1000000000000) (-4187795864 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3412169148 / 1000000000000) (3412169189 / 1000000000000)
      | 1 => orderedInterval (-5382535104 / 1000000000000) (-5382532398 / 1000000000000)
      | 2 => orderedInterval (2716210034 / 1000000000000) (2716211574 / 1000000000000)
      | 3 => orderedInterval (8133508133 / 1000000000000) (8133508543 / 1000000000000)
      | 4 => orderedInterval (-5634568677 / 1000000000000) (-5634567856 / 1000000000000)
      | 5 => orderedInterval (-1104997366 / 1000000000000) (-1104996351 / 1000000000000)
      | 6 => orderedInterval (-7440349904 / 1000000000000) (-7440348418 / 1000000000000)
      | 7 => orderedInterval (200345941 / 1000000000000) (200346226 / 1000000000000)
      | _ => orderedInterval (-16997180966 / 1000000000000) (-16997175936 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-25160733776 / 1000000000000) (-25160733732 / 1000000000000)
      | 1 => orderedInterval (8934178025 / 1000000000000) (8934182043 / 1000000000000)
      | 2 => orderedInterval (7340483605 / 1000000000000) (7340485863 / 1000000000000)
      | 3 => orderedInterval (-8801906687 / 1000000000000) (-8801905789 / 1000000000000)
      | 4 => orderedInterval (19203058581 / 1000000000000) (19203059847 / 1000000000000)
      | 5 => orderedInterval (4338575697 / 1000000000000) (4338577176 / 1000000000000)
      | 6 => orderedInterval (4946849892 / 1000000000000) (4946851410 / 1000000000000)
      | 7 => orderedInterval (4626306246 / 1000000000000) (4626306415 / 1000000000000)
      | _ => orderedInterval (-600094982 / 1000000000000) (-600088694 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-3369166077 / 1000000000000) (-3369166029 / 1000000000000)
      | 1 => orderedInterval (12162768302 / 1000000000000) (12162774489 / 1000000000000)
      | 2 => orderedInterval (-7089095746 / 1000000000000) (-7089092416 / 1000000000000)
      | 3 => orderedInterval (-24178426286 / 1000000000000) (-24178424294 / 1000000000000)
      | 4 => orderedInterval (13678773795 / 1000000000000) (13678775762 / 1000000000000)
      | 5 => orderedInterval (8246749564 / 1000000000000) (8246751733 / 1000000000000)
      | 6 => orderedInterval (7728627044 / 1000000000000) (7728628601 / 1000000000000)
      | 7 => orderedInterval (46181184 / 1000000000000) (46181307 / 1000000000000)
      | _ => orderedInterval (41725756264 / 1000000000000) (41725764174 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13263078556 / 1000000000000) (13263088278 / 1000000000000)
    | 1 => orderedInterval (-3895781920 / 1000000000000) (-3895771353 / 1000000000000)
    | 2 => orderedInterval (-22097398761 / 1000000000000) (-22097385427 / 1000000000000)
    | 3 => orderedInterval (14826716601 / 1000000000000) (14826734539 / 1000000000000)
    | _ => orderedInterval (48952168044 / 1000000000000) (48952193327 / 1000000000000)

theorem compactCertificate360_stateChecks0 :
    compactCertificate360.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (463 / 2)) (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (682087408878163 / 4000000000000)) (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (220573053660979 / 800000000000)) (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks1 :
    compactCertificate360.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (199031404760441 / 4000000000000)) (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (534626349269477 / 4000000000000)) (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1451614537902609 / 4000000000000)) (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks2 :
    compactCertificate360.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1069252698539417 / 4000000000000)) (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1832182723775741 / 4000000000000)) (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1349577501782519 / 4000000000000)) (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks3 :
    compactCertificate360.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2070598947164537 / 4000000000000)) (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1195460859529073 / 4000000000000)) (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2121366273568357 / 4000000000000)) (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks4 :
    compactCertificate360.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1982055549163033 / 4000000000000)) (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1414488364509289 / 4000000000000)) (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1603879047808431 / 4000000000000)) (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks5 :
    compactCertificate360.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1337147137266239 / 4000000000000)) (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1181410047379019 / 4000000000000)) (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (342418679398881 / 800000000000)) (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks6 :
    compactCertificate360.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (947148087725107 / 4000000000000)) (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (802907923342427 / 4000000000000)) (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (502422498217481 / 4000000000000)) (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks7 :
    compactCertificate360.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (270204490523127 / 4000000000000)) (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (733657754030381 / 4000000000000)) (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1001746940797837 / 4000000000000)) (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_stateChecks8 :
    compactCertificate360.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (423577501782519 / 4000000000000)) (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1721819028426199 / 4000000000000)) (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1150095314898041 / 4000000000000)) (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_states : ∀ j,
    BesselStateValid (compactCertificate360.point j) (compactCertificate360.state j) :=
  compactCertificate360.statesValid_of_checks3 compactCertificate360_stateChecks0
    compactCertificate360_stateChecks1 compactCertificate360_stateChecks2
    compactCertificate360_stateChecks3 compactCertificate360_stateChecks4
    compactCertificate360_stateChecks5 compactCertificate360_stateChecks6
    compactCertificate360_stateChecks7 compactCertificate360_stateChecks8

theorem compactCertificate360_chunkChecks0_0 :
    compactCertificate360.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (463 / 2) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (682087408878163 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (220573053660979 / 800000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000)))) (orderedInterval (-3303759498 / 1000000000000) (-3303759461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (199031404760441 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (534626349269477 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1451614537902609 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000)))) (orderedInterval (3185304790 / 1000000000000) (3185306468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1069252698539417 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1832182723775741 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1349577501782519 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000)))) (orderedInterval (-1122773138 / 1000000000000) (-1122772421 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks0_1 :
    compactCertificate360.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2070598947164537 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1195460859529073 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2121366273568357 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000)))) (orderedInterval (-3703651299 / 1000000000000) (-3703651207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1982055549163033 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1414488364509289 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1603879047808431 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000)))) (orderedInterval (2361386040 / 1000000000000) (2361386387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1337147137266239 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1181410047379019 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (342418679398881 / 800000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000)))) (orderedInterval (-525200969 / 1000000000000) (-525200488 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks0_2 :
    compactCertificate360.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (947148087725107 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (802907923342427 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (502422498217481 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000)))) (orderedInterval (7847428084 / 1000000000000) (7847429508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (270204490523127 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (733657754030381 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1001746940797837 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000)))) (orderedInterval (446493937 / 1000000000000) (446495654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (423577501782519 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1721819028426199 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1150095314898041 / 4000000000000) 0 (IntervalRat.scale (463 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000)))) (orderedInterval (8077850609 / 1000000000000) (8077853838 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks0 :
    compactCertificate360.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate360.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate360_chunkChecks0_0
    compactCertificate360_chunkChecks0_1 compactCertificate360_chunkChecks0_2

theorem compactCertificate360_chunkChecks1_0 :
    compactCertificate360.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (463 / 2) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (682087408878163 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (220573053660979 / 800000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000)))) (orderedInterval (23724603461 / 1000000000000) (23724603500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (199031404760441 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (534626349269477 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1451614537902609 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000)))) (orderedInterval (-4880395450 / 1000000000000) (-4880393485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1069252698539417 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1832182723775741 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1349577501782519 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000)))) (orderedInterval (-1567533900 / 1000000000000) (-1567532851 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks1_1 :
    compactCertificate360.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2070598947164537 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1195460859529073 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2121366273568357 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000)))) (orderedInterval (1237522611 / 1000000000000) (1237522802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1982055549163033 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1414488364509289 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1603879047808431 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000)))) (orderedInterval (-6795291408 / 1000000000000) (-6795290876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1337147137266239 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1181410047379019 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (342418679398881 / 800000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000)))) (orderedInterval (-2601323494 / 1000000000000) (-2601322797 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks1_2 :
    compactCertificate360.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (947148087725107 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (802907923342427 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (502422498217481 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000)))) (orderedInterval (-4724046638 / 1000000000000) (-4724045187 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (270204490523127 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (733657754030381 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1001746940797837 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000)))) (orderedInterval (-4101517218 / 1000000000000) (-4101516595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (423577501782519 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1721819028426199 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1150095314898041 / 4000000000000) 1 (IntervalRat.scale (463 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000)))) (orderedInterval (-4187799884 / 1000000000000) (-4187795864 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks1 :
    compactCertificate360.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate360.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate360_chunkChecks1_0
    compactCertificate360_chunkChecks1_1 compactCertificate360_chunkChecks1_2

theorem compactCertificate360_chunkChecks2_0 :
    compactCertificate360.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (463 / 2) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (682087408878163 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (220573053660979 / 800000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000)))) (orderedInterval (3412169148 / 1000000000000) (3412169189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (199031404760441 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (534626349269477 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1451614537902609 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000)))) (orderedInterval (-5382535104 / 1000000000000) (-5382532398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1069252698539417 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1832182723775741 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1349577501782519 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000)))) (orderedInterval (2716210034 / 1000000000000) (2716211574 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks2_1 :
    compactCertificate360.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2070598947164537 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1195460859529073 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2121366273568357 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000)))) (orderedInterval (8133508133 / 1000000000000) (8133508543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1982055549163033 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1414488364509289 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1603879047808431 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000)))) (orderedInterval (-5634568677 / 1000000000000) (-5634567856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1337147137266239 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1181410047379019 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (342418679398881 / 800000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000)))) (orderedInterval (-1104997366 / 1000000000000) (-1104996351 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks2_2 :
    compactCertificate360.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (947148087725107 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (802907923342427 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (502422498217481 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000)))) (orderedInterval (-7440349904 / 1000000000000) (-7440348418 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (270204490523127 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (733657754030381 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1001746940797837 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000)))) (orderedInterval (200345941 / 1000000000000) (200346226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (423577501782519 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1721819028426199 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1150095314898041 / 4000000000000) 2 (IntervalRat.scale (463 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000)))) (orderedInterval (-16997180966 / 1000000000000) (-16997175936 / 1000000000000))) = true
  rfl'

theorem compactCertificate360_chunkChecks2 :
    compactCertificate360.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate360.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate360_chunkChecks2_0
    compactCertificate360_chunkChecks2_1 compactCertificate360_chunkChecks2_2

theorem compactCertificate360_chunkChecks3_0 :
    compactCertificate360.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (463 / 2) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (682087408878163 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (220573053660979 / 800000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000)))) (orderedInterval (-25160733776 / 1000000000000) (-25160733732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (199031404760441 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (534626349269477 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1451614537902609 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000)))) (orderedInterval (8934178025 / 1000000000000) (8934182043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1069252698539417 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1832182723775741 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1349577501782519 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000)))) (orderedInterval (7340483605 / 1000000000000) (7340485863 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate360_chunkChecks3_1 :
    compactCertificate360.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2070598947164537 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1195460859529073 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2121366273568357 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000)))) (orderedInterval (-8801906687 / 1000000000000) (-8801905789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1982055549163033 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1414488364509289 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1603879047808431 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000)))) (orderedInterval (19203058581 / 1000000000000) (19203059847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1337147137266239 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1181410047379019 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (342418679398881 / 800000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000)))) (orderedInterval (4338575697 / 1000000000000) (4338577176 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate360_chunkChecks3_2 :
    compactCertificate360.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (947148087725107 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (802907923342427 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (502422498217481 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000)))) (orderedInterval (4946849892 / 1000000000000) (4946851410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (270204490523127 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (733657754030381 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1001746940797837 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000)))) (orderedInterval (4626306246 / 1000000000000) (4626306415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (423577501782519 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1721819028426199 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1150095314898041 / 4000000000000) 3 (IntervalRat.scale (463 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000)))) (orderedInterval (-600094982 / 1000000000000) (-600088694 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate360_chunkChecks3 :
    compactCertificate360.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate360.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate360_chunkChecks3_0
    compactCertificate360_chunkChecks3_1 compactCertificate360_chunkChecks3_2

theorem compactCertificate360_chunkChecks4_0 :
    compactCertificate360.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (463 / 2) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10058141394 / 1000000000000) (-10058141348 / 1000000000000), orderedInterval (51488384315 / 1000000000000) (51488384362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (682087408878163 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60855366136 / 1000000000000) (60855366331 / 1000000000000), orderedInterval (-5652962590 / 1000000000000) (-5652962395 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (220573053660979 / 800000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1974769084 / 1000000000000) (1974769085 / 1000000000000), orderedInterval (48007570571 / 1000000000000) (48007570572 / 1000000000000)))) (orderedInterval (-3369166077 / 1000000000000) (-3369166029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (199031404760441 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30742268834 / 1000000000000) (30742268835 / 1000000000000), orderedInterval (108547996892 / 1000000000000) (108547996893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (534626349269477 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41625790189 / 1000000000000) (41625808258 / 1000000000000), orderedInterval (-55204817299 / 1000000000000) (-55204799231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1451614537902609 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28119530612 / 1000000000000) (-28119516686 / 1000000000000), orderedInterval (31079542480 / 1000000000000) (31079556405 / 1000000000000)))) (orderedInterval (12162768302 / 1000000000000) (12162774489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1069252698539417 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42636859643 / 1000000000000) (-42636859642 / 1000000000000), orderedInterval (-23661486004 / 1000000000000) (-23661486003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1832182723775741 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5876157005 / 1000000000000) (5876157006 / 1000000000000), orderedInterval (36808425625 / 1000000000000) (36808425626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1349577501782519 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38957625253 / 1000000000000) (-38957596139 / 1000000000000), orderedInterval (19271634684 / 1000000000000) (19271663798 / 1000000000000)))) (orderedInterval (-7089095746 / 1000000000000) (-7089092416 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate360_chunkChecks4_1 :
    compactCertificate360.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2070598947164537 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2526473689 / 1000000000000) (-2526473688 / 1000000000000), orderedInterval (-34975335291 / 1000000000000) (-34975335290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1195460859529073 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42998066871 / 1000000000000) (-42998066870 / 1000000000000), orderedInterval (-16699689515 / 1000000000000) (-16699689514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2121366273568357 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6800788806 / 1000000000000) (-6800788805 / 1000000000000), orderedInterval (-33966305712 / 1000000000000) (-33966305711 / 1000000000000)))) (orderedInterval (-24178426286 / 1000000000000) (-24178424294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1982055549163033 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2600179678 / 1000000000000) (-2600179676 / 1000000000000), orderedInterval (35751840136 / 1000000000000) (35751840137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1414488364509289 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23706063753 / 1000000000000) (23706067113 / 1000000000000), orderedInterval (-35223092057 / 1000000000000) (-35223088697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1603879047808431 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14372169856 / 1000000000000) (-14372169689 / 1000000000000), orderedInterval (37181638525 / 1000000000000) (37181638691 / 1000000000000)))) (orderedInterval (13678773795 / 1000000000000) (13678775762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1337147137266239 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38459494636 / 1000000000000) (38459533721 / 1000000000000), orderedInterval (-20679778380 / 1000000000000) (-20679739295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1181410047379019 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34190119211 / 1000000000000) (34190119212 / 1000000000000), orderedInterval (31350605102 / 1000000000000) (31350605103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (342418679398881 / 800000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38559222266 / 1000000000000) (38559222526 / 1000000000000), orderedInterval (685427145 / 1000000000000) (685427405 / 1000000000000)))) (orderedInterval (8246749564 / 1000000000000) (8246751733 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate360_chunkChecks4_2 :
    compactCertificate360.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (947148087725107 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48120842625 / 1000000000000) (-48120834085 / 1000000000000), orderedInterval (19413676292 / 1000000000000) (19413684831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (802907923342427 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24486983183 / 1000000000000) (24486983184 / 1000000000000), orderedInterval (50653541803 / 1000000000000) (50653541804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (502422498217481 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47280595855 / 1000000000000) (47280595856 / 1000000000000), orderedInterval (53037273022 / 1000000000000) (53037273023 / 1000000000000)))) (orderedInterval (7728627044 / 1000000000000) (7728628601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (270204490523127 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68297906777 / 1000000000000) (-68297826683 / 1000000000000), orderedInterval (69495818426 / 1000000000000) (69495898520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (733657754030381 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53890230764 / 1000000000000) (53890239965 / 1000000000000), orderedInterval (-23953839245 / 1000000000000) (-23953830043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1001746940797837 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5323239094 / 1000000000000) (-5323239083 / 1000000000000), orderedInterval (50147504292 / 1000000000000) (50147504303 / 1000000000000)))) (orderedInterval (46181184 / 1000000000000) (46181307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (423577501782519 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10478332775 / 1000000000000) (-10478332725 / 1000000000000), orderedInterval (76874643021 / 1000000000000) (76874643072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1721819028426199 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28679651378 / 1000000000000) (-28679651377 / 1000000000000), orderedInterval (-25587469161 / 1000000000000) (-25587469160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1150095314898041 / 4000000000000) 4 (IntervalRat.scale (463 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30946828996 / 1000000000000) (-30946812136 / 1000000000000), orderedInterval (35500116790 / 1000000000000) (35500133650 / 1000000000000)))) (orderedInterval (41725756264 / 1000000000000) (41725764174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate360_chunkChecks4 :
    compactCertificate360.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate360.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate360_chunkChecks4_0
    compactCertificate360_chunkChecks4_1 compactCertificate360_chunkChecks4_2

theorem compactCertificate360_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate360.chunkCheck r b = true :=
  compactCertificate360.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate360_chunkChecks0
    · exact compactCertificate360_chunkChecks1
    · exact compactCertificate360_chunkChecks2
    · exact compactCertificate360_chunkChecks3
    · exact compactCertificate360_chunkChecks4)

theorem compactCertificate360_coefficient0 :
    compactCertificate360.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate360_coefficient1 :
    compactCertificate360.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate360_coefficient2 :
    compactCertificate360.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate360_coefficient3 :
    compactCertificate360.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate360_coefficient4 :
    compactCertificate360.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate360_coefficients : ∀ r : Fin 5,
    compactCertificate360.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate360_coefficient0
  · exact compactCertificate360_coefficient1
  · exact compactCertificate360_coefficient2
  · exact compactCertificate360_coefficient3
  · exact compactCertificate360_coefficient4

theorem compactCertificate360_lower : (1 : ℚ) ≤ compactCertificate360.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate360, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate360_proves {t : ℝ} (ht : t ∈ compactCertificate360.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate360.proves compactCertificate360_states compactCertificate360_chunks
    compactCertificate360_coefficients compactCertificate360_lower ht

end Erdos232
