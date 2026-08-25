/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate339 : CompactCertificate where
  left := 211
  right := 212
  center := 423 / 2
  grid := fun i =>
    match i.val with
    | 0 => 67
    | 1 => 50
    | 2 => 80
    | 3 => 14
    | 4 => 39
    | 5 => 106
    | 6 => 78
    | 7 => 133
    | 8 => 98
    | 9 => 151
    | 10 => 87
    | 11 => 154
    | 12 => 144
    | 13 => 103
    | 14 => 117
    | 15 => 97
    | 16 => 86
    | 17 => 125
    | 18 => 69
    | 19 => 58
    | 20 => 37
    | 21 => 20
    | 22 => 53
    | 23 => 73
    | 24 => 31
    | 25 => 125
    | _ => 84
  point := fun i =>
    match i.val with
    | 0 => 423 / 2
    | 1 => 623159770962123 / 4000000000000
    | 2 => 201517066303659 / 800000000000
    | 3 => 181836466984161 / 4000000000000
    | 4 => 488438327734317 / 4000000000000
    | 5 => 1326205074584889 / 4000000000000
    | 6 => 976876655469057 / 4000000000000
    | 7 => 1673894799475461 / 4000000000000
    | 8 => 1232983333161999 / 4000000000000
    | 9 => 1891713508964577 / 4000000000000
    | 10 => 1092181303630233 / 4000000000000
    | 11 => 1938094889242797 / 4000000000000
    | 12 => 1810819648587393 / 4000000000000
    | 13 => 1292286345977169 / 4000000000000
    | 14 => 1465314983202951 / 4000000000000
    | 15 => 1221626866228119 / 4000000000000
    | 16 => 1079344384538499 / 4000000000000
    | 17 => 312836072107401 / 800000000000
    | 18 => 865321039109547 / 4000000000000
    | 19 => 733542228021267 / 4000000000000
    | 20 => 459016666838001 / 4000000000000
    | 21 => 246860690045967 / 4000000000000
    | 22 => 670274794718901 / 4000000000000
    | 23 => 915202928633877 / 4000000000000
    | 24 => 386983333161999 / 4000000000000
    | 25 => 1573065764631279 / 4000000000000
    | _ => 1050735028513761 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))
    | 1 => (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))
    | 2 => (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000))
    | 3 => (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))
    | 4 => (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))
    | 5 => (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000))
    | 6 => (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))
    | 7 => (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))
    | 8 => (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000))
    | 9 => (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))
    | 10 => (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))
    | 11 => (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000))
    | 12 => (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))
    | 13 => (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))
    | 14 => (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000))
    | 15 => (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))
    | 16 => (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))
    | 17 => (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000))
    | 18 => (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))
    | 19 => (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))
    | 20 => (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000))
    | 21 => (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))
    | 22 => (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))
    | 23 => (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000))
    | 24 => (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))
    | 25 => (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))
    | _ => (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18594015854 / 1000000000000) (-18594015247 / 1000000000000)
      | 1 => orderedInterval (-8511473 / 1000000000000) (-8510156 / 1000000000000)
      | 2 => orderedInterval (2195242655 / 1000000000000) (2195242669 / 1000000000000)
      | 3 => orderedInterval (-643545394 / 1000000000000) (-643544589 / 1000000000000)
      | 4 => orderedInterval (-1825784189 / 1000000000000) (-1825784160 / 1000000000000)
      | 5 => orderedInterval (-929104950 / 1000000000000) (-929103852 / 1000000000000)
      | 6 => orderedInterval (1409839520 / 1000000000000) (1409841015 / 1000000000000)
      | 7 => orderedInterval (2955669510 / 1000000000000) (2955669597 / 1000000000000)
      | _ => orderedInterval (6938219711 / 1000000000000) (6938219927 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6084790142 / 1000000000000) (6084790741 / 1000000000000)
      | 1 => orderedInterval (-5062597763 / 1000000000000) (-5062596621 / 1000000000000)
      | 2 => orderedInterval (982907380 / 1000000000000) (982907404 / 1000000000000)
      | 3 => orderedInterval (8220664092 / 1000000000000) (8220665879 / 1000000000000)
      | 4 => orderedInterval (-6498866753 / 1000000000000) (-6498866706 / 1000000000000)
      | 5 => orderedInterval (-4519720741 / 1000000000000) (-4519718720 / 1000000000000)
      | 6 => orderedInterval (8430941052 / 1000000000000) (8430942010 / 1000000000000)
      | 7 => orderedInterval (3409749984 / 1000000000000) (3409750048 / 1000000000000)
      | _ => orderedInterval (-9369657169 / 1000000000000) (-9369656889 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17227817948 / 1000000000000) (17227818546 / 1000000000000)
      | 1 => orderedInterval (-4379874740 / 1000000000000) (-4379873145 / 1000000000000)
      | 2 => orderedInterval (-6799645526 / 1000000000000) (-6799645483 / 1000000000000)
      | 3 => orderedInterval (-3936555720 / 1000000000000) (-3936551729 / 1000000000000)
      | 4 => orderedInterval (5709286124 / 1000000000000) (5709286202 / 1000000000000)
      | 5 => orderedInterval (360592652 / 1000000000000) (360596385 / 1000000000000)
      | 6 => orderedInterval (-1248882463 / 1000000000000) (-1248881809 / 1000000000000)
      | 7 => orderedInterval (-2079756619 / 1000000000000) (-2079756567 / 1000000000000)
      | _ => orderedInterval (-16872265178 / 1000000000000) (-16872264810 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6303834550 / 1000000000000) (-6303833954 / 1000000000000)
      | 1 => orderedInterval (9882794762 / 1000000000000) (9882797215 / 1000000000000)
      | 2 => orderedInterval (-2661507661 / 1000000000000) (-2661507584 / 1000000000000)
      | 3 => orderedInterval (-54688024628 / 1000000000000) (-54688015712 / 1000000000000)
      | 4 => orderedInterval (16390157405 / 1000000000000) (16390157537 / 1000000000000)
      | 5 => orderedInterval (9605724386 / 1000000000000) (9605731274 / 1000000000000)
      | 6 => orderedInterval (-9249851801 / 1000000000000) (-9249851330 / 1000000000000)
      | 7 => orderedInterval (-4710003247 / 1000000000000) (-4710003201 / 1000000000000)
      | _ => orderedInterval (11726211296 / 1000000000000) (11726211792 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-15414963601 / 1000000000000) (-15414963002 / 1000000000000)
      | 1 => orderedInterval (11517102365 / 1000000000000) (11517106211 / 1000000000000)
      | 2 => orderedInterval (22805077689 / 1000000000000) (22805077833 / 1000000000000)
      | 3 => orderedInterval (36434459378 / 1000000000000) (36434479357 / 1000000000000)
      | 4 => orderedInterval (-19805984530 / 1000000000000) (-19805984302 / 1000000000000)
      | 5 => orderedInterval (3686692693 / 1000000000000) (3686705444 / 1000000000000)
      | 6 => orderedInterval (1689859853 / 1000000000000) (1689860213 / 1000000000000)
      | 7 => orderedInterval (1944903948 / 1000000000000) (1944903991 / 1000000000000)
      | _ => orderedInterval (47171005527 / 1000000000000) (47171006215 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-8501990464 / 1000000000000) (-8501984796 / 1000000000000)
    | 1 => orderedInterval (1678210224 / 1000000000000) (1678217146 / 1000000000000)
    | 2 => orderedInterval (-12019283522 / 1000000000000) (-12019272410 / 1000000000000)
    | 3 => orderedInterval (-30008334038 / 1000000000000) (-30008313963 / 1000000000000)
    | _ => orderedInterval (90028153322 / 1000000000000) (90028191960 / 1000000000000)

theorem compactCertificate339_stateChecks0 :
    compactCertificate339.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (423 / 2)) (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (623159770962123 / 4000000000000)) (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201517066303659 / 800000000000)) (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks1 :
    compactCertificate339.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (181836466984161 / 4000000000000)) (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (488438327734317 / 4000000000000)) (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1326205074584889 / 4000000000000)) (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks2 :
    compactCertificate339.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (976876655469057 / 4000000000000)) (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1673894799475461 / 4000000000000)) (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1232983333161999 / 4000000000000)) (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks3 :
    compactCertificate339.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1891713508964577 / 4000000000000)) (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1092181303630233 / 4000000000000)) (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1938094889242797 / 4000000000000)) (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks4 :
    compactCertificate339.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1810819648587393 / 4000000000000)) (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1292286345977169 / 4000000000000)) (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1465314983202951 / 4000000000000)) (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks5 :
    compactCertificate339.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221626866228119 / 4000000000000)) (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1079344384538499 / 4000000000000)) (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (312836072107401 / 800000000000)) (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks6 :
    compactCertificate339.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (865321039109547 / 4000000000000)) (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (733542228021267 / 4000000000000)) (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (459016666838001 / 4000000000000)) (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks7 :
    compactCertificate339.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (246860690045967 / 4000000000000)) (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (670274794718901 / 4000000000000)) (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (915202928633877 / 4000000000000)) (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_stateChecks8 :
    compactCertificate339.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (386983333161999 / 4000000000000)) (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1573065764631279 / 4000000000000)) (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1050735028513761 / 4000000000000)) (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_states : ∀ j,
    BesselStateValid (compactCertificate339.point j) (compactCertificate339.state j) :=
  compactCertificate339.statesValid_of_checks3 compactCertificate339_stateChecks0
    compactCertificate339_stateChecks1 compactCertificate339_stateChecks2
    compactCertificate339_stateChecks3 compactCertificate339_stateChecks4
    compactCertificate339_stateChecks5 compactCertificate339_stateChecks6
    compactCertificate339_stateChecks7 compactCertificate339_stateChecks8

theorem compactCertificate339_chunkChecks0_0 :
    compactCertificate339.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (423 / 2) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (623159770962123 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (201517066303659 / 800000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000)))) (orderedInterval (-18594015854 / 1000000000000) (-18594015247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (181836466984161 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (488438327734317 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1326205074584889 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000)))) (orderedInterval (-8511473 / 1000000000000) (-8510156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (976876655469057 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1673894799475461 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1232983333161999 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000)))) (orderedInterval (2195242655 / 1000000000000) (2195242669 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks0_1 :
    compactCertificate339.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1891713508964577 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1092181303630233 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1938094889242797 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000)))) (orderedInterval (-643545394 / 1000000000000) (-643544589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1810819648587393 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1292286345977169 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1465314983202951 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000)))) (orderedInterval (-1825784189 / 1000000000000) (-1825784160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1221626866228119 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1079344384538499 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (312836072107401 / 800000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000)))) (orderedInterval (-929104950 / 1000000000000) (-929103852 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks0_2 :
    compactCertificate339.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (865321039109547 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (733542228021267 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (459016666838001 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000)))) (orderedInterval (1409839520 / 1000000000000) (1409841015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (246860690045967 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (670274794718901 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (915202928633877 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000)))) (orderedInterval (2955669510 / 1000000000000) (2955669597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (386983333161999 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1573065764631279 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1050735028513761 / 4000000000000) 0 (IntervalRat.scale (423 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000)))) (orderedInterval (6938219711 / 1000000000000) (6938219927 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks0 :
    compactCertificate339.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate339.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate339_chunkChecks0_0
    compactCertificate339_chunkChecks0_1 compactCertificate339_chunkChecks0_2

theorem compactCertificate339_chunkChecks1_0 :
    compactCertificate339.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (423 / 2) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (623159770962123 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (201517066303659 / 800000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000)))) (orderedInterval (6084790142 / 1000000000000) (6084790741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (181836466984161 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (488438327734317 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1326205074584889 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000)))) (orderedInterval (-5062597763 / 1000000000000) (-5062596621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (976876655469057 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1673894799475461 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1232983333161999 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000)))) (orderedInterval (982907380 / 1000000000000) (982907404 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks1_1 :
    compactCertificate339.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1891713508964577 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1092181303630233 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1938094889242797 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000)))) (orderedInterval (8220664092 / 1000000000000) (8220665879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1810819648587393 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1292286345977169 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1465314983202951 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000)))) (orderedInterval (-6498866753 / 1000000000000) (-6498866706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1221626866228119 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1079344384538499 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (312836072107401 / 800000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000)))) (orderedInterval (-4519720741 / 1000000000000) (-4519718720 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks1_2 :
    compactCertificate339.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (865321039109547 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (733542228021267 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (459016666838001 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000)))) (orderedInterval (8430941052 / 1000000000000) (8430942010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (246860690045967 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (670274794718901 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (915202928633877 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000)))) (orderedInterval (3409749984 / 1000000000000) (3409750048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (386983333161999 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1573065764631279 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1050735028513761 / 4000000000000) 1 (IntervalRat.scale (423 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000)))) (orderedInterval (-9369657169 / 1000000000000) (-9369656889 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks1 :
    compactCertificate339.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate339.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate339_chunkChecks1_0
    compactCertificate339_chunkChecks1_1 compactCertificate339_chunkChecks1_2

theorem compactCertificate339_chunkChecks2_0 :
    compactCertificate339.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (423 / 2) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (623159770962123 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (201517066303659 / 800000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000)))) (orderedInterval (17227817948 / 1000000000000) (17227818546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (181836466984161 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (488438327734317 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1326205074584889 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000)))) (orderedInterval (-4379874740 / 1000000000000) (-4379873145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (976876655469057 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1673894799475461 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1232983333161999 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000)))) (orderedInterval (-6799645526 / 1000000000000) (-6799645483 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks2_1 :
    compactCertificate339.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1891713508964577 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1092181303630233 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1938094889242797 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000)))) (orderedInterval (-3936555720 / 1000000000000) (-3936551729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1810819648587393 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1292286345977169 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1465314983202951 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000)))) (orderedInterval (5709286124 / 1000000000000) (5709286202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1221626866228119 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1079344384538499 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (312836072107401 / 800000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000)))) (orderedInterval (360592652 / 1000000000000) (360596385 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks2_2 :
    compactCertificate339.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (865321039109547 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (733542228021267 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (459016666838001 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000)))) (orderedInterval (-1248882463 / 1000000000000) (-1248881809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (246860690045967 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (670274794718901 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (915202928633877 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000)))) (orderedInterval (-2079756619 / 1000000000000) (-2079756567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (386983333161999 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1573065764631279 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1050735028513761 / 4000000000000) 2 (IntervalRat.scale (423 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000)))) (orderedInterval (-16872265178 / 1000000000000) (-16872264810 / 1000000000000))) = true
  rfl'

theorem compactCertificate339_chunkChecks2 :
    compactCertificate339.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate339.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate339_chunkChecks2_0
    compactCertificate339_chunkChecks2_1 compactCertificate339_chunkChecks2_2

theorem compactCertificate339_chunkChecks3_0 :
    compactCertificate339.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (423 / 2) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (623159770962123 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (201517066303659 / 800000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000)))) (orderedInterval (-6303834550 / 1000000000000) (-6303833954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (181836466984161 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (488438327734317 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1326205074584889 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000)))) (orderedInterval (9882794762 / 1000000000000) (9882797215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (976876655469057 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1673894799475461 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1232983333161999 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000)))) (orderedInterval (-2661507661 / 1000000000000) (-2661507584 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate339_chunkChecks3_1 :
    compactCertificate339.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1891713508964577 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1092181303630233 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1938094889242797 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000)))) (orderedInterval (-54688024628 / 1000000000000) (-54688015712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1810819648587393 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1292286345977169 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1465314983202951 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000)))) (orderedInterval (16390157405 / 1000000000000) (16390157537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1221626866228119 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1079344384538499 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (312836072107401 / 800000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000)))) (orderedInterval (9605724386 / 1000000000000) (9605731274 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate339_chunkChecks3_2 :
    compactCertificate339.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (865321039109547 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (733542228021267 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (459016666838001 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000)))) (orderedInterval (-9249851801 / 1000000000000) (-9249851330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (246860690045967 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (670274794718901 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (915202928633877 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000)))) (orderedInterval (-4710003247 / 1000000000000) (-4710003201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (386983333161999 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1573065764631279 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1050735028513761 / 4000000000000) 3 (IntervalRat.scale (423 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000)))) (orderedInterval (11726211296 / 1000000000000) (11726211792 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate339_chunkChecks3 :
    compactCertificate339.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate339.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate339_chunkChecks3_0
    compactCertificate339_chunkChecks3_1 compactCertificate339_chunkChecks3_2

theorem compactCertificate339_chunkChecks4_0 :
    compactCertificate339.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (423 / 2) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-53452378704 / 1000000000000) (-53452377301 / 1000000000000), orderedInterval (12489950817 / 1000000000000) (12489952219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (623159770962123 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30932550938 / 1000000000000) (-30932547107 / 1000000000000), orderedInterval (56041985149 / 1000000000000) (56041988980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (201517066303659 / 800000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (49093579811 / 1000000000000) (49093579815 / 1000000000000), orderedInterval (10724960619 / 1000000000000) (10724960623 / 1000000000000)))) (orderedInterval (-15414963601 / 1000000000000) (-15414963002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (181836466984161 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91365963210 / 1000000000000) (91366025242 / 1000000000000), orderedInterval (-76213332670 / 1000000000000) (-76213270638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (488438327734317 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26234228546 / 1000000000000) (-26234228545 / 1000000000000), orderedInterval (-67163001124 / 1000000000000) (-67163001123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1326205074584889 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27297974997 / 1000000000000) (-27297966310 / 1000000000000), orderedInterval (34318647163 / 1000000000000) (34318655851 / 1000000000000)))) (orderedInterval (11517102365 / 1000000000000) (11517106211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (976876655469057 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2050727815 / 1000000000000) (-2050727811 / 1000000000000), orderedInterval (51019450824 / 1000000000000) (51019450828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1673894799475461 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38601016549 / 1000000000000) (-38601016507 / 1000000000000), orderedInterval (-5544074285 / 1000000000000) (-5544074243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1232983333161999 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41568675395 / 1000000000000) (41568675397 / 1000000000000), orderedInterval (18299452088 / 1000000000000) (18299452090 / 1000000000000)))) (orderedInterval (22805077689 / 1000000000000) (22805077833 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate339_chunkChecks4_1 :
    compactCertificate339.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1891713508964577 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22696722792 / 1000000000000) (22696726688 / 1000000000000), orderedInterval (-28850754036 / 1000000000000) (-28850750140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1092181303630233 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23644020161 / 1000000000000) (-23644020160 / 1000000000000), orderedInterval (-42057959756 / 1000000000000) (-42057959755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1938094889242797 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36166044157 / 1000000000000) (36166044357 / 1000000000000), orderedInterval (2396793641 / 1000000000000) (2396793841 / 1000000000000)))) (orderedInterval (36434459378 / 1000000000000) (36434479357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1810819648587393 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33432121543 / 1000000000000) (33432121544 / 1000000000000), orderedInterval (16949848044 / 1000000000000) (16949848045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1292286345977169 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-11949597880 / 1000000000000) (-11949597879 / 1000000000000), orderedInterval (-42733482281 / 1000000000000) (-42733482280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1465314983202951 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18227763978 / 1000000000000) (18227764594 / 1000000000000), orderedInterval (-37516037468 / 1000000000000) (-37516036852 / 1000000000000)))) (orderedInterval (-19805984530 / 1000000000000) (-19805984302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1221626866228119 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-45362108147 / 1000000000000) (-45362108119 / 1000000000000), orderedInterval (-5100162072 / 1000000000000) (-5100162043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1079344384538499 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20867281568 / 1000000000000) (20867281569 / 1000000000000), orderedInterval (43822960624 / 1000000000000) (43822960625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (312836072107401 / 800000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30811140391 / 1000000000000) (30811182428 / 1000000000000), orderedInterval (-26090671454 / 1000000000000) (-26090629418 / 1000000000000)))) (orderedInterval (3686692693 / 1000000000000) (3686705444 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate339_chunkChecks4_2 :
    compactCertificate339.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (865321039109547 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18355919175 / 1000000000000) (-18355919174 / 1000000000000), orderedInterval (-51005400616 / 1000000000000) (-51005400615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (733542228021267 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54559537357 / 1000000000000) (54559544220 / 1000000000000), orderedInterval (-22391282702 / 1000000000000) (-22391275839 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (459016666838001 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48008649884 / 1000000000000) (48008682218 / 1000000000000), orderedInterval (-57155307538 / 1000000000000) (-57155275204 / 1000000000000)))) (orderedInterval (1689859853 / 1000000000000) (1689860213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (246860690045967 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-33228511752 / 1000000000000) (-33228510825 / 1000000000000), orderedInterval (96246176926 / 1000000000000) (96246177853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (670274794718901 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59268246242 / 1000000000000) (-59268244294 / 1000000000000), orderedInterval (17100721747 / 1000000000000) (17100723695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (915202928633877 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13015467263 / 1000000000000) (-13015467262 / 1000000000000), orderedInterval (-51089300027 / 1000000000000) (-51089300026 / 1000000000000)))) (orderedInterval (1944903948 / 1000000000000) (1944903991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (386983333161999 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11365117311 / 1000000000000) (-11365117309 / 1000000000000), orderedInterval (-80260946140 / 1000000000000) (-80260946139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1573065764631279 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-39278926982 / 1000000000000) (-39278926971 / 1000000000000), orderedInterval (-8665842763 / 1000000000000) (-8665842752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1050735028513761 / 4000000000000) 4 (IntervalRat.scale (423 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-20302875924 / 1000000000000) (-20302875089 / 1000000000000), orderedInterval (44886362320 / 1000000000000) (44886363156 / 1000000000000)))) (orderedInterval (47171005527 / 1000000000000) (47171006215 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate339_chunkChecks4 :
    compactCertificate339.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate339.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate339_chunkChecks4_0
    compactCertificate339_chunkChecks4_1 compactCertificate339_chunkChecks4_2

theorem compactCertificate339_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate339.chunkCheck r b = true :=
  compactCertificate339.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate339_chunkChecks0
    · exact compactCertificate339_chunkChecks1
    · exact compactCertificate339_chunkChecks2
    · exact compactCertificate339_chunkChecks3
    · exact compactCertificate339_chunkChecks4)

theorem compactCertificate339_coefficient0 :
    compactCertificate339.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate339_coefficient1 :
    compactCertificate339.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate339_coefficient2 :
    compactCertificate339.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate339_coefficient3 :
    compactCertificate339.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate339_coefficient4 :
    compactCertificate339.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate339_coefficients : ∀ r : Fin 5,
    compactCertificate339.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate339_coefficient0
  · exact compactCertificate339_coefficient1
  · exact compactCertificate339_coefficient2
  · exact compactCertificate339_coefficient3
  · exact compactCertificate339_coefficient4

theorem compactCertificate339_lower : (1 : ℚ) ≤ compactCertificate339.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate339, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate339_proves {t : ℝ} (ht : t ∈ compactCertificate339.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate339.proves compactCertificate339_states compactCertificate339_chunks
    compactCertificate339_coefficients compactCertificate339_lower ht

end Erdos232
