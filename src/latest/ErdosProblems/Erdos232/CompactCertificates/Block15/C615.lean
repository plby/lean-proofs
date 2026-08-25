/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate615 : CompactCertificate where
  left := 486
  right := 487
  center := 973 / 2
  grid := fun i =>
    match i.val with
    | 0 => 155
    | 1 => 114
    | 2 => 185
    | 3 => 33
    | 4 => 89
    | 5 => 243
    | 6 => 179
    | 7 => 307
    | 8 => 226
    | 9 => 346
    | 10 => 200
    | 11 => 355
    | 12 => 332
    | 13 => 237
    | 14 => 268
    | 15 => 224
    | 16 => 198
    | 17 => 286
    | 18 => 158
    | 19 => 134
    | 20 => 84
    | 21 => 45
    | 22 => 123
    | 23 => 168
    | 24 => 71
    | 25 => 288
    | _ => 192
  point := fun i =>
    match i.val with
    | 0 => 973 / 2
    | 1 => 1433414792307673 / 4000000000000
    | 2 => 463536892466809 / 800000000000
    | 3 => 418266861408011 / 4000000000000
    | 4 => 1123523623842767 / 4000000000000
    | 5 => 3050585195203539 / 4000000000000
    | 6 => 2247047247686507 / 4000000000000
    | 7 => 3850353758604311 / 4000000000000
    | 8 => 2836153151694149 / 4000000000000
    | 9 => 4351388284214027 / 4000000000000
    | 10 => 2512275197239283 / 4000000000000
    | 11 => 4458076423719247 / 4000000000000
    | 12 => 4165313281502443 / 4000000000000
    | 13 => 2972564100793819 / 4000000000000
    | 14 => 3370570871528301 / 4000000000000
    | 15 => 2810030593002269 / 4000000000000
    | 16 => 2482747248595649 / 4000000000000
    | 17 => 719596922365251 / 800000000000
    | 18 => 1990442957573497 / 4000000000000
    | 19 => 1687320538687217 / 4000000000000
    | 20 => 1055846848305851 / 4000000000000
    | 21 => 567837946606917 / 4000000000000
    | 22 => 1541790485251751 / 4000000000000
    | 23 => 2105183095888327 / 4000000000000
    | 24 => 890153151694149 / 4000000000000
    | 25 => 3618423141811429 / 4000000000000
    | _ => 2416938966297611 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))
    | 1 => (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))
    | 2 => (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000))
    | 3 => (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))
    | 4 => (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))
    | 5 => (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000))
    | 6 => (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))
    | 7 => (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))
    | 8 => (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000))
    | 9 => (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))
    | 10 => (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))
    | 11 => (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000))
    | 12 => (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))
    | 13 => (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))
    | 14 => (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000))
    | 15 => (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))
    | 16 => (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))
    | 17 => (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000))
    | 18 => (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))
    | 19 => (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))
    | 20 => (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000))
    | 21 => (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))
    | 22 => (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))
    | 23 => (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000))
    | 24 => (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))
    | 25 => (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))
    | _ => (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2804074054 / 1000000000000) (-2804070969 / 1000000000000)
      | 1 => orderedInterval (-638999593 / 1000000000000) (-638998404 / 1000000000000)
      | 2 => orderedInterval (-832301915 / 1000000000000) (-832301160 / 1000000000000)
      | 3 => orderedInterval (-3216660872 / 1000000000000) (-3216655842 / 1000000000000)
      | 4 => orderedInterval (1843060284 / 1000000000000) (1843060436 / 1000000000000)
      | 5 => orderedInterval (1501182336 / 1000000000000) (1501183500 / 1000000000000)
      | 6 => orderedInterval (-6130201854 / 1000000000000) (-6130192466 / 1000000000000)
      | 7 => orderedInterval (2774925513 / 1000000000000) (2774925913 / 1000000000000)
      | _ => orderedInterval (-7207507932 / 1000000000000) (-7207504677 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14640028846 / 1000000000000) (-14640025174 / 1000000000000)
      | 1 => orderedInterval (3675171308 / 1000000000000) (3675172027 / 1000000000000)
      | 2 => orderedInterval (1758462135 / 1000000000000) (1758463621 / 1000000000000)
      | 3 => orderedInterval (-4478004068 / 1000000000000) (-4477992854 / 1000000000000)
      | 4 => orderedInterval (-4034160583 / 1000000000000) (-4034160322 / 1000000000000)
      | 5 => orderedInterval (-1789778126 / 1000000000000) (-1789776009 / 1000000000000)
      | 6 => orderedInterval (3274797068 / 1000000000000) (3274806652 / 1000000000000)
      | 7 => orderedInterval (-1406509009 / 1000000000000) (-1406508587 / 1000000000000)
      | _ => orderedInterval (-1451425538 / 1000000000000) (-1451421474 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2305291112 / 1000000000000) (2305295491 / 1000000000000)
      | 1 => orderedInterval (340153313 / 1000000000000) (340153783 / 1000000000000)
      | 2 => orderedInterval (3027108313 / 1000000000000) (3027111246 / 1000000000000)
      | 3 => orderedInterval (20137375198 / 1000000000000) (20137400259 / 1000000000000)
      | 4 => orderedInterval (-4982888133 / 1000000000000) (-4982887671 / 1000000000000)
      | 5 => orderedInterval (-3566098821 / 1000000000000) (-3566094949 / 1000000000000)
      | 6 => orderedInterval (6666287793 / 1000000000000) (6666297600 / 1000000000000)
      | 7 => orderedInterval (-2020227699 / 1000000000000) (-2020227246 / 1000000000000)
      | _ => orderedInterval (13383223689 / 1000000000000) (13383228789 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15240850750 / 1000000000000) (15240855964 / 1000000000000)
      | 1 => orderedInterval (-8068531253 / 1000000000000) (-8068530897 / 1000000000000)
      | 2 => orderedInterval (-5029410286 / 1000000000000) (-5029404496 / 1000000000000)
      | 3 => orderedInterval (33004835503 / 1000000000000) (33004891504 / 1000000000000)
      | 4 => orderedInterval (10781701793 / 1000000000000) (10781702631 / 1000000000000)
      | 5 => orderedInterval (3193853883 / 1000000000000) (3193860984 / 1000000000000)
      | 6 => orderedInterval (-2971202479 / 1000000000000) (-2971192458 / 1000000000000)
      | 7 => orderedInterval (2115822494 / 1000000000000) (2115822981 / 1000000000000)
      | _ => orderedInterval (8311221560 / 1000000000000) (8311227979 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1455483187 / 1000000000000) (-1455476967 / 1000000000000)
      | 1 => orderedInterval (168939979 / 1000000000000) (168940318 / 1000000000000)
      | 2 => orderedInterval (-11360685501 / 1000000000000) (-11360674053 / 1000000000000)
      | 3 => orderedInterval (-107635812516 / 1000000000000) (-107635687211 / 1000000000000)
      | 4 => orderedInterval (14912292881 / 1000000000000) (14912294444 / 1000000000000)
      | 5 => orderedInterval (9734781020 / 1000000000000) (9734794088 / 1000000000000)
      | 6 => orderedInterval (-6750150782 / 1000000000000) (-6750140520 / 1000000000000)
      | 7 => orderedInterval (2304130575 / 1000000000000) (2304131101 / 1000000000000)
      | _ => orderedInterval (-28867824618 / 1000000000000) (-28867816476 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-14710578087 / 1000000000000) (-14710553669 / 1000000000000)
    | 1 => orderedInterval (-19091475659 / 1000000000000) (-19091442120 / 1000000000000)
    | 2 => orderedInterval (35290224765 / 1000000000000) (35290277302 / 1000000000000)
    | 3 => orderedInterval (56579141965 / 1000000000000) (56579234192 / 1000000000000)
    | _ => orderedInterval (-128949812149 / 1000000000000) (-128949635276 / 1000000000000)

theorem compactCertificate615_stateChecks0 :
    compactCertificate615.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (973 / 2)) (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1433414792307673 / 4000000000000)) (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (463536892466809 / 800000000000)) (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks1 :
    compactCertificate615.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (418266861408011 / 4000000000000)) (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1123523623842767 / 4000000000000)) (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3050585195203539 / 4000000000000)) (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks2 :
    compactCertificate615.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2247047247686507 / 4000000000000)) (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 307 12 (3850353758604311 / 4000000000000)) (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2836153151694149 / 4000000000000)) (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks3 :
    compactCertificate615.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 346 12 (4351388284214027 / 4000000000000)) (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2512275197239283 / 4000000000000)) (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 355 12 (4458076423719247 / 4000000000000)) (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks4 :
    compactCertificate615.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 332 12 (4165313281502443 / 4000000000000)) (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2972564100793819 / 4000000000000)) (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (3370570871528301 / 4000000000000)) (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks5 :
    compactCertificate615.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2810030593002269 / 4000000000000)) (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2482747248595649 / 4000000000000)) (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (719596922365251 / 800000000000)) (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks6 :
    compactCertificate615.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1990442957573497 / 4000000000000)) (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1687320538687217 / 4000000000000)) (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1055846848305851 / 4000000000000)) (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks7 :
    compactCertificate615.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (567837946606917 / 4000000000000)) (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1541790485251751 / 4000000000000)) (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2105183095888327 / 4000000000000)) (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_stateChecks8 :
    compactCertificate615.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (890153151694149 / 4000000000000)) (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (3618423141811429 / 4000000000000)) (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2416938966297611 / 4000000000000)) (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_states : ∀ j,
    BesselStateValid (compactCertificate615.point j) (compactCertificate615.state j) :=
  compactCertificate615.statesValid_of_checks3 compactCertificate615_stateChecks0
    compactCertificate615_stateChecks1 compactCertificate615_stateChecks2
    compactCertificate615_stateChecks3 compactCertificate615_stateChecks4
    compactCertificate615_stateChecks5 compactCertificate615_stateChecks6
    compactCertificate615_stateChecks7 compactCertificate615_stateChecks8

theorem compactCertificate615_chunkChecks0_0 :
    compactCertificate615.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (973 / 2) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1433414792307673 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (463536892466809 / 800000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000)))) (orderedInterval (-2804074054 / 1000000000000) (-2804070969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (418266861408011 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1123523623842767 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3050585195203539 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000)))) (orderedInterval (-638999593 / 1000000000000) (-638998404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2247047247686507 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3850353758604311 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2836153151694149 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000)))) (orderedInterval (-832301915 / 1000000000000) (-832301160 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks0_1 :
    compactCertificate615.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4351388284214027 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2512275197239283 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4458076423719247 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000)))) (orderedInterval (-3216660872 / 1000000000000) (-3216655842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4165313281502443 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2972564100793819 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3370570871528301 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000)))) (orderedInterval (1843060284 / 1000000000000) (1843060436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2810030593002269 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2482747248595649 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (719596922365251 / 800000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000)))) (orderedInterval (1501182336 / 1000000000000) (1501183500 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks0_2 :
    compactCertificate615.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1990442957573497 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1687320538687217 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1055846848305851 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000)))) (orderedInterval (-6130201854 / 1000000000000) (-6130192466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (567837946606917 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1541790485251751 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2105183095888327 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000)))) (orderedInterval (2774925513 / 1000000000000) (2774925913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (890153151694149 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3618423141811429 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2416938966297611 / 4000000000000) 0 (IntervalRat.scale (973 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000)))) (orderedInterval (-7207507932 / 1000000000000) (-7207504677 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks0 :
    compactCertificate615.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate615.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate615_chunkChecks0_0
    compactCertificate615_chunkChecks0_1 compactCertificate615_chunkChecks0_2

theorem compactCertificate615_chunkChecks1_0 :
    compactCertificate615.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (973 / 2) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1433414792307673 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (463536892466809 / 800000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000)))) (orderedInterval (-14640028846 / 1000000000000) (-14640025174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (418266861408011 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1123523623842767 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3050585195203539 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000)))) (orderedInterval (3675171308 / 1000000000000) (3675172027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2247047247686507 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3850353758604311 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2836153151694149 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000)))) (orderedInterval (1758462135 / 1000000000000) (1758463621 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks1_1 :
    compactCertificate615.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4351388284214027 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2512275197239283 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4458076423719247 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000)))) (orderedInterval (-4478004068 / 1000000000000) (-4477992854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4165313281502443 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2972564100793819 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3370570871528301 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000)))) (orderedInterval (-4034160583 / 1000000000000) (-4034160322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2810030593002269 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2482747248595649 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (719596922365251 / 800000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000)))) (orderedInterval (-1789778126 / 1000000000000) (-1789776009 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks1_2 :
    compactCertificate615.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1990442957573497 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1687320538687217 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1055846848305851 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000)))) (orderedInterval (3274797068 / 1000000000000) (3274806652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (567837946606917 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1541790485251751 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2105183095888327 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000)))) (orderedInterval (-1406509009 / 1000000000000) (-1406508587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (890153151694149 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3618423141811429 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2416938966297611 / 4000000000000) 1 (IntervalRat.scale (973 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000)))) (orderedInterval (-1451425538 / 1000000000000) (-1451421474 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks1 :
    compactCertificate615.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate615.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate615_chunkChecks1_0
    compactCertificate615_chunkChecks1_1 compactCertificate615_chunkChecks1_2

theorem compactCertificate615_chunkChecks2_0 :
    compactCertificate615.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (973 / 2) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1433414792307673 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (463536892466809 / 800000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000)))) (orderedInterval (2305291112 / 1000000000000) (2305295491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (418266861408011 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1123523623842767 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3050585195203539 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000)))) (orderedInterval (340153313 / 1000000000000) (340153783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2247047247686507 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3850353758604311 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2836153151694149 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000)))) (orderedInterval (3027108313 / 1000000000000) (3027111246 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks2_1 :
    compactCertificate615.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4351388284214027 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2512275197239283 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4458076423719247 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000)))) (orderedInterval (20137375198 / 1000000000000) (20137400259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4165313281502443 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2972564100793819 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3370570871528301 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000)))) (orderedInterval (-4982888133 / 1000000000000) (-4982887671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2810030593002269 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2482747248595649 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (719596922365251 / 800000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000)))) (orderedInterval (-3566098821 / 1000000000000) (-3566094949 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks2_2 :
    compactCertificate615.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1990442957573497 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1687320538687217 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1055846848305851 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000)))) (orderedInterval (6666287793 / 1000000000000) (6666297600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (567837946606917 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1541790485251751 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2105183095888327 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000)))) (orderedInterval (-2020227699 / 1000000000000) (-2020227246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (890153151694149 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3618423141811429 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2416938966297611 / 4000000000000) 2 (IntervalRat.scale (973 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000)))) (orderedInterval (13383223689 / 1000000000000) (13383228789 / 1000000000000))) = true
  rfl'

theorem compactCertificate615_chunkChecks2 :
    compactCertificate615.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate615.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate615_chunkChecks2_0
    compactCertificate615_chunkChecks2_1 compactCertificate615_chunkChecks2_2

theorem compactCertificate615_chunkChecks3_0 :
    compactCertificate615.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (973 / 2) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1433414792307673 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (463536892466809 / 800000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000)))) (orderedInterval (15240850750 / 1000000000000) (15240855964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (418266861408011 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1123523623842767 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3050585195203539 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000)))) (orderedInterval (-8068531253 / 1000000000000) (-8068530897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2247047247686507 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3850353758604311 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2836153151694149 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000)))) (orderedInterval (-5029410286 / 1000000000000) (-5029404496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate615_chunkChecks3_1 :
    compactCertificate615.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4351388284214027 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2512275197239283 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4458076423719247 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000)))) (orderedInterval (33004835503 / 1000000000000) (33004891504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4165313281502443 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2972564100793819 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3370570871528301 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000)))) (orderedInterval (10781701793 / 1000000000000) (10781702631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2810030593002269 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2482747248595649 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (719596922365251 / 800000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000)))) (orderedInterval (3193853883 / 1000000000000) (3193860984 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate615_chunkChecks3_2 :
    compactCertificate615.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1990442957573497 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1687320538687217 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1055846848305851 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000)))) (orderedInterval (-2971202479 / 1000000000000) (-2971192458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (567837946606917 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1541790485251751 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2105183095888327 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000)))) (orderedInterval (2115822494 / 1000000000000) (2115822981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (890153151694149 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3618423141811429 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2416938966297611 / 4000000000000) 3 (IntervalRat.scale (973 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000)))) (orderedInterval (8311221560 / 1000000000000) (8311227979 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate615_chunkChecks3 :
    compactCertificate615.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate615.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate615_chunkChecks3_0
    compactCertificate615_chunkChecks3_1 compactCertificate615_chunkChecks3_2

theorem compactCertificate615_chunkChecks4_0 :
    compactCertificate615.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (973 / 2) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12004939033 / 1000000000000) (-12004939032 / 1000000000000), orderedInterval (-34111743449 / 1000000000000) (-34111743448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1433414792307673 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35402636840 / 1000000000000) (35402636841 / 1000000000000), orderedInterval (22823403218 / 1000000000000) (22823403219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (463536892466809 / 800000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27681460248 / 1000000000000) (27681512236 / 1000000000000), orderedInterval (-18257179548 / 1000000000000) (-18257127560 / 1000000000000)))) (orderedInterval (-1455483187 / 1000000000000) (-1455476967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (418266861408011 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77575320369 / 1000000000000) (-77575320210 / 1000000000000), orderedInterval (8747687840 / 1000000000000) (8747687999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1123523623842767 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41931448182 / 1000000000000) (-41931417271 / 1000000000000), orderedInterval (22619344618 / 1000000000000) (22619375529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3050585195203539 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-708311340 / 1000000000000) (-708311339 / 1000000000000), orderedInterval (-28882913018 / 1000000000000) (-28882913017 / 1000000000000)))) (orderedInterval (168939979 / 1000000000000) (168940318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2247047247686507 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6750735168 / 1000000000000) (-6750735167 / 1000000000000), orderedInterval (-32974041225 / 1000000000000) (-32974041224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3850353758604311 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22863311988 / 1000000000000) (22863335555 / 1000000000000), orderedInterval (-11786042911 / 1000000000000) (-11786019344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2836153151694149 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5259227675 / 1000000000000) (-5259227673 / 1000000000000), orderedInterval (29502937142 / 1000000000000) (29502937143 / 1000000000000)))) (orderedInterval (-11360685501 / 1000000000000) (-11360674053 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate615_chunkChecks4_1 :
    compactCertificate615.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4351388284214027 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24131021033 / 1000000000000) (24131048252 / 1000000000000), orderedInterval (-1715163145 / 1000000000000) (-1715135926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2512275197239283 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16244776638 / 1000000000000) (16244776639 / 1000000000000), orderedInterval (27368121235 / 1000000000000) (27368121236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4458076423719247 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-931858174 / 1000000000000) (-931858173 / 1000000000000), orderedInterval (-23881321687 / 1000000000000) (-23881321686 / 1000000000000)))) (orderedInterval (-107635812516 / 1000000000000) (-107635687211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4165313281502443 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19293622989 / 1000000000000) (-19293620974 / 1000000000000), orderedInterval (15472435029 / 1000000000000) (15472437044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2972564100793819 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17271995041 / 1000000000000) (17271995570 / 1000000000000), orderedInterval (-23640819651 / 1000000000000) (-23640819122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3370570871528301 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27376020138 / 1000000000000) (27376021585 / 1000000000000), orderedInterval (2444882191 / 1000000000000) (2444883638 / 1000000000000)))) (orderedInterval (14912292881 / 1000000000000) (14912294444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2810030593002269 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12381665263 / 1000000000000) (-12381665222 / 1000000000000), orderedInterval (27447926288 / 1000000000000) (27447926330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2482747248595649 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17102248132 / 1000000000000) (-17102247640 / 1000000000000), orderedInterval (27091131487 / 1000000000000) (27091131979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (719596922365251 / 800000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25990401573 / 1000000000000) (25990444079 / 1000000000000), orderedInterval (-5693316580 / 1000000000000) (-5693274074 / 1000000000000)))) (orderedInterval (9734781020 / 1000000000000) (9734794088 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate615_chunkChecks4_2 :
    compactCertificate615.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1990442957573497 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32153315502 / 1000000000000) (32153373176 / 1000000000000), orderedInterval (-15701252825 / 1000000000000) (-15701195151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1687320538687217 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38750274519 / 1000000000000) (38750275296 / 1000000000000), orderedInterval (-2802793394 / 1000000000000) (-2802792618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1055846848305851 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36987664454 / 1000000000000) (36987664455 / 1000000000000), orderedInterval (32236290160 / 1000000000000) (32236290161 / 1000000000000)))) (orderedInterval (-6750150782 / 1000000000000) (-6750140520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (567837946606917 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65651854413 / 1000000000000) (-65651854411 / 1000000000000), orderedInterval (-12972012347 / 1000000000000) (-12972012345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1541790485251751 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7403779312 / 1000000000000) (7403779324 / 1000000000000), orderedInterval (-39969870868 / 1000000000000) (-39969870856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2105183095888327 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22581559856 / 1000000000000) (-22581555399 / 1000000000000), orderedInterval (26473235575 / 1000000000000) (26473240032 / 1000000000000)))) (orderedInterval (2304130575 / 1000000000000) (2304131101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (890153151694149 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14268670314 / 1000000000000) (-14268670313 / 1000000000000), orderedInterval (-51515311950 / 1000000000000) (-51515311949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3618423141811429 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15248531638 / 1000000000000) (15248531639 / 1000000000000), orderedInterval (21699545703 / 1000000000000) (21699545704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2416938966297611 / 4000000000000) 4 (IntervalRat.scale (973 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31340083097 / 1000000000000) (31340099727 / 1000000000000), orderedInterval (-8475504857 / 1000000000000) (-8475488227 / 1000000000000)))) (orderedInterval (-28867824618 / 1000000000000) (-28867816476 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate615_chunkChecks4 :
    compactCertificate615.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate615.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate615_chunkChecks4_0
    compactCertificate615_chunkChecks4_1 compactCertificate615_chunkChecks4_2

theorem compactCertificate615_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate615.chunkCheck r b = true :=
  compactCertificate615.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate615_chunkChecks0
    · exact compactCertificate615_chunkChecks1
    · exact compactCertificate615_chunkChecks2
    · exact compactCertificate615_chunkChecks3
    · exact compactCertificate615_chunkChecks4)

theorem compactCertificate615_coefficient0 :
    compactCertificate615.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate615_coefficient1 :
    compactCertificate615.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate615_coefficient2 :
    compactCertificate615.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate615_coefficient3 :
    compactCertificate615.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate615_coefficient4 :
    compactCertificate615.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate615_coefficients : ∀ r : Fin 5,
    compactCertificate615.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate615_coefficient0
  · exact compactCertificate615_coefficient1
  · exact compactCertificate615_coefficient2
  · exact compactCertificate615_coefficient3
  · exact compactCertificate615_coefficient4

theorem compactCertificate615_lower : (1 : ℚ) ≤ compactCertificate615.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate615, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate615_proves {t : ℝ} (ht : t ∈ compactCertificate615.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate615.proves compactCertificate615_states compactCertificate615_chunks
    compactCertificate615_coefficients compactCertificate615_lower ht

end Erdos232
