/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate468 : CompactCertificate where
  left := 339
  right := 340
  center := 679 / 2
  grid := fun i =>
    match i.val with
    | 0 => 108
    | 1 => 80
    | 2 => 129
    | 3 => 23
    | 4 => 62
    | 5 => 169
    | 6 => 125
    | 7 => 214
    | 8 => 158
    | 9 => 242
    | 10 => 140
    | 11 => 248
    | 12 => 231
    | 13 => 165
    | 14 => 187
    | 15 => 156
    | 16 => 138
    | 17 => 200
    | 18 => 111
    | 19 => 94
    | 20 => 59
    | 21 => 32
    | 22 => 86
    | 23 => 117
    | 24 => 49
    | 25 => 201
    | _ => 134
  point := fun i =>
    match i.val with
    | 0 => 679 / 2
    | 1 => 1000296653624779 / 4000000000000
    | 2 => 323475385390507 / 800000000000
    | 3 => 291884068752353 / 4000000000000
    | 4 => 784041665559341 / 4000000000000
    | 5 => 2128825639818297 / 4000000000000
    | 6 => 1568083331119361 / 4000000000000
    | 7 => 2686937514997253 / 4000000000000
    | 8 => 1979186012333327 / 4000000000000
    | 9 => 3036580313444321 / 4000000000000
    | 10 => 1753170461382809 / 4000000000000
    | 11 => 3111031748926381 / 4000000000000
    | 12 => 2906729412271489 / 4000000000000
    | 13 => 2074379264582737 / 4000000000000
    | 14 => 2352124996678023 / 4000000000000
    | 15 => 1960956600872087 / 4000000000000
    | 16 => 1732564626717827 / 4000000000000
    | 17 => 502164758772873 / 800000000000
    | 18 => 1389014150249131 / 4000000000000
    | 19 => 1177482678076691 / 4000000000000
    | 20 => 736813987666673 / 4000000000000
    | 21 => 396261013099791 / 4000000000000
    | 22 => 1075925734312373 / 4000000000000
    | 23 => 1469084606483221 / 4000000000000
    | 24 => 621186012333327 / 4000000000000
    | 25 => 2525086652918767 / 4000000000000
    | _ => 1686640861373153 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))
    | 1 => (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))
    | 2 => (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000))
    | 3 => (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))
    | 4 => (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))
    | 5 => (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000))
    | 6 => (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))
    | 7 => (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))
    | 8 => (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000))
    | 9 => (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))
    | 10 => (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))
    | 11 => (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000))
    | 12 => (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))
    | 13 => (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))
    | 14 => (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000))
    | 15 => (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))
    | 16 => (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))
    | 17 => (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000))
    | 18 => (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))
    | 19 => (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))
    | 20 => (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000))
    | 21 => (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))
    | 22 => (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))
    | 23 => (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000))
    | 24 => (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))
    | 25 => (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))
    | _ => (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14481613523 / 1000000000000) (14481613562 / 1000000000000)
      | 1 => orderedInterval (5055782329 / 1000000000000) (5055789453 / 1000000000000)
      | 2 => orderedInterval (-821868700 / 1000000000000) (-821868383 / 1000000000000)
      | 3 => orderedInterval (-2423584123 / 1000000000000) (-2423583183 / 1000000000000)
      | 4 => orderedInterval (-2131425144 / 1000000000000) (-2131424837 / 1000000000000)
      | 5 => orderedInterval (-351881538 / 1000000000000) (-351881505 / 1000000000000)
      | 6 => orderedInterval (-3206834705 / 1000000000000) (-3206833240 / 1000000000000)
      | 7 => orderedInterval (2874414474 / 1000000000000) (2874415070 / 1000000000000)
      | _ => orderedInterval (-6126625958 / 1000000000000) (-6126625634 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6914409375 / 1000000000000) (6914409413 / 1000000000000)
      | 1 => orderedInterval (-2328889280 / 1000000000000) (-2328878604 / 1000000000000)
      | 2 => orderedInterval (-943491224 / 1000000000000) (-943490758 / 1000000000000)
      | 3 => orderedInterval (-348056622 / 1000000000000) (-348055275 / 1000000000000)
      | 4 => orderedInterval (-2806118101 / 1000000000000) (-2806117464 / 1000000000000)
      | 5 => orderedInterval (-750486898 / 1000000000000) (-750486850 / 1000000000000)
      | 6 => orderedInterval (2232584700 / 1000000000000) (2232586180 / 1000000000000)
      | 7 => orderedInterval (1904397975 / 1000000000000) (1904398181 / 1000000000000)
      | _ => orderedInterval (3186549899 / 1000000000000) (3186550149 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14731296832 / 1000000000000) (-14731296793 / 1000000000000)
      | 1 => orderedInterval (-5992224490 / 1000000000000) (-5992208006 / 1000000000000)
      | 2 => orderedInterval (2117527740 / 1000000000000) (2117528431 / 1000000000000)
      | 3 => orderedInterval (6282062666 / 1000000000000) (6282064713 / 1000000000000)
      | 4 => orderedInterval (3693626418 / 1000000000000) (3693627750 / 1000000000000)
      | 5 => orderedInterval (170922947 / 1000000000000) (170923017 / 1000000000000)
      | 6 => orderedInterval (3981925521 / 1000000000000) (3981927028 / 1000000000000)
      | 7 => orderedInterval (-2118505987 / 1000000000000) (-2118505894 / 1000000000000)
      | _ => orderedInterval (6227120380 / 1000000000000) (6227120645 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5579496932 / 1000000000000) (-5579496890 / 1000000000000)
      | 1 => orderedInterval (4669470599 / 1000000000000) (4669496275 / 1000000000000)
      | 2 => orderedInterval (5281486864 / 1000000000000) (5281487893 / 1000000000000)
      | 3 => orderedInterval (8716233505 / 1000000000000) (8716236836 / 1000000000000)
      | 4 => orderedInterval (6977145805 / 1000000000000) (6977148608 / 1000000000000)
      | 5 => orderedInterval (-1600992498 / 1000000000000) (-1600992390 / 1000000000000)
      | 6 => orderedInterval (-3741328815 / 1000000000000) (-3741327280 / 1000000000000)
      | 7 => orderedInterval (-3023296038 / 1000000000000) (-3023295978 / 1000000000000)
      | _ => orderedInterval (-12414902935 / 1000000000000) (-12414902583 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14983919619 / 1000000000000) (14983919667 / 1000000000000)
      | 1 => orderedInterval (13272736134 / 1000000000000) (13272776364 / 1000000000000)
      | 2 => orderedInterval (-5967692867 / 1000000000000) (-5967691323 / 1000000000000)
      | 3 => orderedInterval (-23684709045 / 1000000000000) (-23684703171 / 1000000000000)
      | 4 => orderedInterval (-2910267626 / 1000000000000) (-2910261696 / 1000000000000)
      | 5 => orderedInterval (911725488 / 1000000000000) (911725660 / 1000000000000)
      | 6 => orderedInterval (-4391579392 / 1000000000000) (-4391577823 / 1000000000000)
      | 7 => orderedInterval (2254285769 / 1000000000000) (2254285819 / 1000000000000)
      | _ => orderedInterval (160707710 / 1000000000000) (160708241 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7349590158 / 1000000000000) (7349601303 / 1000000000000)
    | 1 => orderedInterval (7060899824 / 1000000000000) (7060914972 / 1000000000000)
    | 2 => orderedInterval (-368841637 / 1000000000000) (-368819109 / 1000000000000)
    | 3 => orderedInterval (-715680445 / 1000000000000) (-715645509 / 1000000000000)
    | _ => orderedInterval (-5370874210 / 1000000000000) (-5370818262 / 1000000000000)

theorem compactCertificate468_stateChecks0 :
    compactCertificate468.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (679 / 2)) (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1000296653624779 / 4000000000000)) (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (323475385390507 / 800000000000)) (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks1 :
    compactCertificate468.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (291884068752353 / 4000000000000)) (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (784041665559341 / 4000000000000)) (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2128825639818297 / 4000000000000)) (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks2 :
    compactCertificate468.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1568083331119361 / 4000000000000)) (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2686937514997253 / 4000000000000)) (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1979186012333327 / 4000000000000)) (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks3 :
    compactCertificate468.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3036580313444321 / 4000000000000)) (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1753170461382809 / 4000000000000)) (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3111031748926381 / 4000000000000)) (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks4 :
    compactCertificate468.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2906729412271489 / 4000000000000)) (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2074379264582737 / 4000000000000)) (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2352124996678023 / 4000000000000)) (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks5 :
    compactCertificate468.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1960956600872087 / 4000000000000)) (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1732564626717827 / 4000000000000)) (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (502164758772873 / 800000000000)) (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks6 :
    compactCertificate468.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1389014150249131 / 4000000000000)) (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1177482678076691 / 4000000000000)) (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (736813987666673 / 4000000000000)) (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks7 :
    compactCertificate468.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (396261013099791 / 4000000000000)) (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1075925734312373 / 4000000000000)) (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1469084606483221 / 4000000000000)) (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_stateChecks8 :
    compactCertificate468.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (621186012333327 / 4000000000000)) (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2525086652918767 / 4000000000000)) (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1686640861373153 / 4000000000000)) (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_states : ∀ j,
    BesselStateValid (compactCertificate468.point j) (compactCertificate468.state j) :=
  compactCertificate468.statesValid_of_checks3 compactCertificate468_stateChecks0
    compactCertificate468_stateChecks1 compactCertificate468_stateChecks2
    compactCertificate468_stateChecks3 compactCertificate468_stateChecks4
    compactCertificate468_stateChecks5 compactCertificate468_stateChecks6
    compactCertificate468_stateChecks7 compactCertificate468_stateChecks8

theorem compactCertificate468_chunkChecks0_0 :
    compactCertificate468.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (679 / 2) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1000296653624779 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (323475385390507 / 800000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000)))) (orderedInterval (14481613523 / 1000000000000) (14481613562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (291884068752353 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (784041665559341 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2128825639818297 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000)))) (orderedInterval (5055782329 / 1000000000000) (5055789453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1568083331119361 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2686937514997253 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1979186012333327 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000)))) (orderedInterval (-821868700 / 1000000000000) (-821868383 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks0_1 :
    compactCertificate468.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3036580313444321 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1753170461382809 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3111031748926381 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000)))) (orderedInterval (-2423584123 / 1000000000000) (-2423583183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2906729412271489 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2074379264582737 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2352124996678023 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000)))) (orderedInterval (-2131425144 / 1000000000000) (-2131424837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1960956600872087 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1732564626717827 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (502164758772873 / 800000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000)))) (orderedInterval (-351881538 / 1000000000000) (-351881505 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks0_2 :
    compactCertificate468.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1389014150249131 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1177482678076691 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (736813987666673 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000)))) (orderedInterval (-3206834705 / 1000000000000) (-3206833240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (396261013099791 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1075925734312373 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1469084606483221 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000)))) (orderedInterval (2874414474 / 1000000000000) (2874415070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (621186012333327 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2525086652918767 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1686640861373153 / 4000000000000) 0 (IntervalRat.scale (679 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000)))) (orderedInterval (-6126625958 / 1000000000000) (-6126625634 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks0 :
    compactCertificate468.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate468.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate468_chunkChecks0_0
    compactCertificate468_chunkChecks0_1 compactCertificate468_chunkChecks0_2

theorem compactCertificate468_chunkChecks1_0 :
    compactCertificate468.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (679 / 2) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1000296653624779 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (323475385390507 / 800000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000)))) (orderedInterval (6914409375 / 1000000000000) (6914409413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (291884068752353 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (784041665559341 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2128825639818297 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000)))) (orderedInterval (-2328889280 / 1000000000000) (-2328878604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1568083331119361 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2686937514997253 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1979186012333327 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000)))) (orderedInterval (-943491224 / 1000000000000) (-943490758 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks1_1 :
    compactCertificate468.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3036580313444321 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1753170461382809 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3111031748926381 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000)))) (orderedInterval (-348056622 / 1000000000000) (-348055275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2906729412271489 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2074379264582737 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2352124996678023 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000)))) (orderedInterval (-2806118101 / 1000000000000) (-2806117464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1960956600872087 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1732564626717827 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (502164758772873 / 800000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000)))) (orderedInterval (-750486898 / 1000000000000) (-750486850 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks1_2 :
    compactCertificate468.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1389014150249131 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1177482678076691 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (736813987666673 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000)))) (orderedInterval (2232584700 / 1000000000000) (2232586180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (396261013099791 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1075925734312373 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1469084606483221 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000)))) (orderedInterval (1904397975 / 1000000000000) (1904398181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (621186012333327 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2525086652918767 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1686640861373153 / 4000000000000) 1 (IntervalRat.scale (679 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000)))) (orderedInterval (3186549899 / 1000000000000) (3186550149 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks1 :
    compactCertificate468.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate468.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate468_chunkChecks1_0
    compactCertificate468_chunkChecks1_1 compactCertificate468_chunkChecks1_2

theorem compactCertificate468_chunkChecks2_0 :
    compactCertificate468.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (679 / 2) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1000296653624779 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (323475385390507 / 800000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000)))) (orderedInterval (-14731296832 / 1000000000000) (-14731296793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (291884068752353 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (784041665559341 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2128825639818297 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000)))) (orderedInterval (-5992224490 / 1000000000000) (-5992208006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1568083331119361 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2686937514997253 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1979186012333327 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000)))) (orderedInterval (2117527740 / 1000000000000) (2117528431 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks2_1 :
    compactCertificate468.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3036580313444321 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1753170461382809 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3111031748926381 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000)))) (orderedInterval (6282062666 / 1000000000000) (6282064713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2906729412271489 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2074379264582737 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2352124996678023 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000)))) (orderedInterval (3693626418 / 1000000000000) (3693627750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1960956600872087 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1732564626717827 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (502164758772873 / 800000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000)))) (orderedInterval (170922947 / 1000000000000) (170923017 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks2_2 :
    compactCertificate468.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1389014150249131 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1177482678076691 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (736813987666673 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000)))) (orderedInterval (3981925521 / 1000000000000) (3981927028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (396261013099791 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1075925734312373 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1469084606483221 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000)))) (orderedInterval (-2118505987 / 1000000000000) (-2118505894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (621186012333327 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2525086652918767 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1686640861373153 / 4000000000000) 2 (IntervalRat.scale (679 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000)))) (orderedInterval (6227120380 / 1000000000000) (6227120645 / 1000000000000))) = true
  rfl'

theorem compactCertificate468_chunkChecks2 :
    compactCertificate468.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate468.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate468_chunkChecks2_0
    compactCertificate468_chunkChecks2_1 compactCertificate468_chunkChecks2_2

theorem compactCertificate468_chunkChecks3_0 :
    compactCertificate468.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (679 / 2) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1000296653624779 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (323475385390507 / 800000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000)))) (orderedInterval (-5579496932 / 1000000000000) (-5579496890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (291884068752353 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (784041665559341 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2128825639818297 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000)))) (orderedInterval (4669470599 / 1000000000000) (4669496275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1568083331119361 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2686937514997253 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1979186012333327 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000)))) (orderedInterval (5281486864 / 1000000000000) (5281487893 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate468_chunkChecks3_1 :
    compactCertificate468.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3036580313444321 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1753170461382809 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3111031748926381 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000)))) (orderedInterval (8716233505 / 1000000000000) (8716236836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2906729412271489 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2074379264582737 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2352124996678023 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000)))) (orderedInterval (6977145805 / 1000000000000) (6977148608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1960956600872087 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1732564626717827 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (502164758772873 / 800000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000)))) (orderedInterval (-1600992498 / 1000000000000) (-1600992390 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate468_chunkChecks3_2 :
    compactCertificate468.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1389014150249131 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1177482678076691 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (736813987666673 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000)))) (orderedInterval (-3741328815 / 1000000000000) (-3741327280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (396261013099791 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1075925734312373 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1469084606483221 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000)))) (orderedInterval (-3023296038 / 1000000000000) (-3023295978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (621186012333327 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2525086652918767 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1686640861373153 / 4000000000000) 3 (IntervalRat.scale (679 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000)))) (orderedInterval (-12414902935 / 1000000000000) (-12414902583 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate468_chunkChecks3 :
    compactCertificate468.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate468.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate468_chunkChecks3_0
    compactCertificate468_chunkChecks3_1 compactCertificate468_chunkChecks3_2

theorem compactCertificate468_chunkChecks4_0 :
    compactCertificate468.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (679 / 2) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36274265862 / 1000000000000) (36274265863 / 1000000000000), orderedInterval (23597063549 / 1000000000000) (23597063550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1000296653624779 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22776201580 / 1000000000000) (-22776200079 / 1000000000000), orderedInterval (45067439056 / 1000000000000) (45067440556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (323475385390507 / 800000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5384939925 / 1000000000000) (5384939930 / 1000000000000), orderedInterval (-39318916138 / 1000000000000) (-39318916133 / 1000000000000)))) (orderedInterval (14983919619 / 1000000000000) (14983919667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (291884068752353 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-93155881712 / 1000000000000) (-93155881703 / 1000000000000), orderedInterval (-6148598262 / 1000000000000) (-6148598253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (784041665559341 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51424295488 / 1000000000000) (51424308629 / 1000000000000), orderedInterval (-24695831211 / 1000000000000) (-24695818070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2128825639818297 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30489995988 / 1000000000000) (-30489903096 / 1000000000000), orderedInterval (16355024027 / 1000000000000) (16355116918 / 1000000000000)))) (orderedInterval (13272736134 / 1000000000000) (13272776364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1568083331119361 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4296884791 / 1000000000000) (-4296884790 / 1000000000000), orderedInterval (-40062983479 / 1000000000000) (-40062983478 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2686937514997253 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6681061019 / 1000000000000) (6681061020 / 1000000000000), orderedInterval (30046468245 / 1000000000000) (30046468246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1979186012333327 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25479863828 / 1000000000000) (-25479851548 / 1000000000000), orderedInterval (25272648810 / 1000000000000) (25272661089 / 1000000000000)))) (orderedInterval (-5967692867 / 1000000000000) (-5967691323 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate468_chunkChecks4_1 :
    compactCertificate468.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3036580313444321 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9523712840 / 1000000000000) (-9523712833 / 1000000000000), orderedInterval (27354032543 / 1000000000000) (27354032550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1753170461382809 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25845447199 / 1000000000000) (-25845436727 / 1000000000000), orderedInterval (28038631349 / 1000000000000) (28038641821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3111031748926381 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15482283924 / 1000000000000) (-15482283728 / 1000000000000), orderedInterval (24068859374 / 1000000000000) (24068859569 / 1000000000000)))) (orderedInterval (-23684709045 / 1000000000000) (-23684703171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2906729412271489 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29071968716 / 1000000000000) (-29071953957 / 1000000000000), orderedInterval (5577351603 / 1000000000000) (5577366361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2074379264582737 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29803508098 / 1000000000000) (-29803508097 / 1000000000000), orderedInterval (-18392359592 / 1000000000000) (-18392359591 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2352124996678023 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32020373587 / 1000000000000) (-32020373547 / 1000000000000), orderedInterval (-7544066313 / 1000000000000) (-7544066272 / 1000000000000)))) (orderedInterval (-2910267626 / 1000000000000) (-2910261696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1960956600872087 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29012443538 / 1000000000000) (29012443539 / 1000000000000), orderedInterval (21344884268 / 1000000000000) (21344884269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1732564626717827 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14450617427 / 1000000000000) (14450617428 / 1000000000000), orderedInterval (35493243234 / 1000000000000) (35493243235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (502164758772873 / 800000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5469982965 / 1000000000000) (5469982966 / 1000000000000), orderedInterval (31368883476 / 1000000000000) (31368883477 / 1000000000000)))) (orderedInterval (911725488 / 1000000000000) (911725660 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate468_chunkChecks4_2 :
    compactCertificate468.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1389014150249131 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26863364175 / 1000000000000) (26863372666 / 1000000000000), orderedInterval (-33380241020 / 1000000000000) (-33380232529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1177482678076691 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7136428450 / 1000000000000) (-7136428435 / 1000000000000), orderedInterval (45965588290 / 1000000000000) (45965588306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (736813987666673 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21025598528 / 1000000000000) (21025599185 / 1000000000000), orderedInterval (-54956993740 / 1000000000000) (-54956993083 / 1000000000000)))) (orderedInterval (-4391579392 / 1000000000000) (-4391577823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (396261013099791 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50504381857 / 1000000000000) (-50504352643 / 1000000000000), orderedInterval (62509141325 / 1000000000000) (62509170538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1075925734312373 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19418971301 / 1000000000000) (-19418970627 / 1000000000000), orderedInterval (44641992805 / 1000000000000) (44641993479 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1469084606483221 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19589148528 / 1000000000000) (-19589148527 / 1000000000000), orderedInterval (-36710836339 / 1000000000000) (-36710836338 / 1000000000000)))) (orderedInterval (2254285769 / 1000000000000) (2254285819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (621186012333327 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53825561337 / 1000000000000) (-53825525713 / 1000000000000), orderedInterval (34845811644 / 1000000000000) (34845847268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2525086652918767 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17845497686 / 1000000000000) (-17845497685 / 1000000000000), orderedInterval (-26253912391 / 1000000000000) (-26253912390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1686640861373153 / 4000000000000) 4 (IntervalRat.scale (679 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38666190203 / 1000000000000) (38666190286 / 1000000000000), orderedInterval (3790554847 / 1000000000000) (3790554930 / 1000000000000)))) (orderedInterval (160707710 / 1000000000000) (160708241 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate468_chunkChecks4 :
    compactCertificate468.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate468.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate468_chunkChecks4_0
    compactCertificate468_chunkChecks4_1 compactCertificate468_chunkChecks4_2

theorem compactCertificate468_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate468.chunkCheck r b = true :=
  compactCertificate468.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate468_chunkChecks0
    · exact compactCertificate468_chunkChecks1
    · exact compactCertificate468_chunkChecks2
    · exact compactCertificate468_chunkChecks3
    · exact compactCertificate468_chunkChecks4)

theorem compactCertificate468_coefficient0 :
    compactCertificate468.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate468_coefficient1 :
    compactCertificate468.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate468_coefficient2 :
    compactCertificate468.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate468_coefficient3 :
    compactCertificate468.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate468_coefficient4 :
    compactCertificate468.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate468_coefficients : ∀ r : Fin 5,
    compactCertificate468.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate468_coefficient0
  · exact compactCertificate468_coefficient1
  · exact compactCertificate468_coefficient2
  · exact compactCertificate468_coefficient3
  · exact compactCertificate468_coefficient4

theorem compactCertificate468_lower : (1 : ℚ) ≤ compactCertificate468.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate468, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate468_proves {t : ℝ} (ht : t ∈ compactCertificate468.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate468.proves compactCertificate468_states compactCertificate468_chunks
    compactCertificate468_coefficients compactCertificate468_lower ht

end Erdos232
