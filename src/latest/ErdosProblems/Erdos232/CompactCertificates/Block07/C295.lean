/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate295 : CompactCertificate where
  left := 168
  right := 169
  center := 337 / 2
  grid := fun i =>
    match i.val with
    | 0 => 54
    | 1 => 40
    | 2 => 64
    | 3 => 12
    | 4 => 31
    | 5 => 84
    | 6 => 62
    | 7 => 106
    | 8 => 78
    | 9 => 120
    | 10 => 69
    | 11 => 123
    | 12 => 115
    | 13 => 82
    | 14 => 93
    | 15 => 77
    | 16 => 68
    | 17 => 99
    | 18 => 55
    | 19 => 47
    | 20 => 29
    | 21 => 16
    | 22 => 43
    | 23 => 58
    | 24 => 25
    | 25 => 100
    | _ => 67
  point := fun i =>
    match i.val with
    | 0 => 337 / 2
    | 1 => 496465349442637 / 4000000000000
    | 2 => 160546693485421 / 800000000000
    | 3 => 144867350765159 / 4000000000000
    | 4 => 389134081433723 / 4000000000000
    | 5 => 1056574728451791 / 4000000000000
    | 6 => 778268162867783 / 4000000000000
    | 7 => 1333575762229859 / 4000000000000
    | 8 => 982305870627881 / 4000000000000
    | 9 => 1507109816834663 / 4000000000000
    | 10 => 870130258447727 / 4000000000000
    | 11 => 1544061412942843 / 4000000000000
    | 12 => 1442662462349767 / 4000000000000
    | 13 => 1029552006133111 / 4000000000000
    | 14 => 1167402244301169 / 4000000000000
    | 15 => 973258283496161 / 4000000000000
    | 16 => 859903209431381 / 4000000000000
    | 17 => 249233466430719 / 800000000000
    | 18 => 689392884586093 / 4000000000000
    | 19 => 584405983080773 / 4000000000000
    | 20 => 365694129372119 / 4000000000000
    | 21 => 196671519020073 / 4000000000000
    | 22 => 534001432199219 / 4000000000000
    | 23 => 729133302481363 / 4000000000000
    | 24 => 308305870627881 / 4000000000000
    | 25 => 1253246247472201 / 4000000000000
    | _ => 837110412787559 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))
    | 1 => (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))
    | 2 => (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000))
    | 3 => (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))
    | 4 => (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))
    | 5 => (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000))
    | 6 => (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))
    | 7 => (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))
    | 8 => (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000))
    | 9 => (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))
    | 10 => (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))
    | 11 => (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000))
    | 12 => (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))
    | 13 => (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))
    | 14 => (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000))
    | 15 => (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))
    | 16 => (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))
    | 17 => (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000))
    | 18 => (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))
    | 19 => (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))
    | 20 => (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000))
    | 21 => (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))
    | 22 => (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))
    | 23 => (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000))
    | 24 => (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))
    | 25 => (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))
    | _ => (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7768474372 / 1000000000000) (-7768473583 / 1000000000000)
      | 1 => orderedInterval (-3926839466 / 1000000000000) (-3926838954 / 1000000000000)
      | 2 => orderedInterval (-49941883 / 1000000000000) (-49941873 / 1000000000000)
      | 3 => orderedInterval (-10122733328 / 1000000000000) (-10122733256 / 1000000000000)
      | 4 => orderedInterval (2740296116 / 1000000000000) (2740296137 / 1000000000000)
      | 5 => orderedInterval (-4232668676 / 1000000000000) (-4232665263 / 1000000000000)
      | 6 => orderedInterval (-1731255329 / 1000000000000) (-1731252354 / 1000000000000)
      | 7 => orderedInterval (-3896922836 / 1000000000000) (-3896921121 / 1000000000000)
      | _ => orderedInterval (-3686045276 / 1000000000000) (-3686044824 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (26784349913 / 1000000000000) (26784350571 / 1000000000000)
      | 1 => orderedInterval (-4346515997 / 1000000000000) (-4346515868 / 1000000000000)
      | 2 => orderedInterval (-589896946 / 1000000000000) (-589896929 / 1000000000000)
      | 3 => orderedInterval (-26087693015 / 1000000000000) (-26087692870 / 1000000000000)
      | 4 => orderedInterval (8035748414 / 1000000000000) (8035748448 / 1000000000000)
      | 5 => orderedInterval (2074388603 / 1000000000000) (2074393122 / 1000000000000)
      | 6 => orderedInterval (11019712080 / 1000000000000) (11019714663 / 1000000000000)
      | 7 => orderedInterval (-2922694512 / 1000000000000) (-2922693158 / 1000000000000)
      | _ => orderedInterval (4719660346 / 1000000000000) (4719660767 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6852046252 / 1000000000000) (6852046818 / 1000000000000)
      | 1 => orderedInterval (7974483787 / 1000000000000) (7974483843 / 1000000000000)
      | 2 => orderedInterval (2332059709 / 1000000000000) (2332059739 / 1000000000000)
      | 3 => orderedInterval (37948987674 / 1000000000000) (37948987980 / 1000000000000)
      | 4 => orderedInterval (-6797016095 / 1000000000000) (-6797016040 / 1000000000000)
      | 5 => orderedInterval (9098342985 / 1000000000000) (9098349018 / 1000000000000)
      | 6 => orderedInterval (-840359584 / 1000000000000) (-840357326 / 1000000000000)
      | 7 => orderedInterval (4671766726 / 1000000000000) (4671767808 / 1000000000000)
      | _ => orderedInterval (5676777817 / 1000000000000) (5676778288 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-28172538935 / 1000000000000) (-28172538440 / 1000000000000)
      | 1 => orderedInterval (7248314774 / 1000000000000) (7248314828 / 1000000000000)
      | 2 => orderedInterval (3095120238 / 1000000000000) (3095120292 / 1000000000000)
      | 3 => orderedInterval (132891165633 / 1000000000000) (132891166296 / 1000000000000)
      | 4 => orderedInterval (-22550822195 / 1000000000000) (-22550822102 / 1000000000000)
      | 5 => orderedInterval (-2674405934 / 1000000000000) (-2674397886 / 1000000000000)
      | 6 => orderedInterval (-11331609796 / 1000000000000) (-11331607835 / 1000000000000)
      | 7 => orderedInterval (3227092589 / 1000000000000) (3227093451 / 1000000000000)
      | _ => orderedInterval (5465072447 / 1000000000000) (5465073030 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-5786701298 / 1000000000000) (-5786700850 / 1000000000000)
      | 1 => orderedInterval (-18410208550 / 1000000000000) (-18410208474 / 1000000000000)
      | 2 => orderedInterval (-13683408362 / 1000000000000) (-13683408262 / 1000000000000)
      | 3 => orderedInterval (-171105966000 / 1000000000000) (-171105964536 / 1000000000000)
      | 4 => orderedInterval (17531391956 / 1000000000000) (17531392116 / 1000000000000)
      | 5 => orderedInterval (-22098257680 / 1000000000000) (-22098246854 / 1000000000000)
      | 6 => orderedInterval (2056372480 / 1000000000000) (2056374196 / 1000000000000)
      | 7 => orderedInterval (-5161145024 / 1000000000000) (-5161144332 / 1000000000000)
      | _ => orderedInterval (-7438524610 / 1000000000000) (-7438523844 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-32674585050 / 1000000000000) (-32674575091 / 1000000000000)
    | 1 => orderedInterval (18687058886 / 1000000000000) (18687068746 / 1000000000000)
    | 2 => orderedInterval (66917089271 / 1000000000000) (66917100128 / 1000000000000)
    | 3 => orderedInterval (87197388821 / 1000000000000) (87197401634 / 1000000000000)
    | _ => orderedInterval (-224096447088 / 1000000000000) (-224096430840 / 1000000000000)

theorem compactCertificate295_stateChecks0 :
    compactCertificate295.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (337 / 2)) (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (496465349442637 / 4000000000000)) (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (160546693485421 / 800000000000)) (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks1 :
    compactCertificate295.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (144867350765159 / 4000000000000)) (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (389134081433723 / 4000000000000)) (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1056574728451791 / 4000000000000)) (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks2 :
    compactCertificate295.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (778268162867783 / 4000000000000)) (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1333575762229859 / 4000000000000)) (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (982305870627881 / 4000000000000)) (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks3 :
    compactCertificate295.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1507109816834663 / 4000000000000)) (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (870130258447727 / 4000000000000)) (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1544061412942843 / 4000000000000)) (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks4 :
    compactCertificate295.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1442662462349767 / 4000000000000)) (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1029552006133111 / 4000000000000)) (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1167402244301169 / 4000000000000)) (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks5 :
    compactCertificate295.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (973258283496161 / 4000000000000)) (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (859903209431381 / 4000000000000)) (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (249233466430719 / 800000000000)) (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks6 :
    compactCertificate295.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (689392884586093 / 4000000000000)) (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584405983080773 / 4000000000000)) (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (365694129372119 / 4000000000000)) (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks7 :
    compactCertificate295.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (196671519020073 / 4000000000000)) (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (534001432199219 / 4000000000000)) (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (729133302481363 / 4000000000000)) (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_stateChecks8 :
    compactCertificate295.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (308305870627881 / 4000000000000)) (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1253246247472201 / 4000000000000)) (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (837110412787559 / 4000000000000)) (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_states : ∀ j,
    BesselStateValid (compactCertificate295.point j) (compactCertificate295.state j) :=
  compactCertificate295.statesValid_of_checks3 compactCertificate295_stateChecks0
    compactCertificate295_stateChecks1 compactCertificate295_stateChecks2
    compactCertificate295_stateChecks3 compactCertificate295_stateChecks4
    compactCertificate295_stateChecks5 compactCertificate295_stateChecks6
    compactCertificate295_stateChecks7 compactCertificate295_stateChecks8

theorem compactCertificate295_chunkChecks0_0 :
    compactCertificate295.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (337 / 2) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (496465349442637 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (160546693485421 / 800000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000)))) (orderedInterval (-7768474372 / 1000000000000) (-7768473583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (144867350765159 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (389134081433723 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1056574728451791 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000)))) (orderedInterval (-3926839466 / 1000000000000) (-3926838954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (778268162867783 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1333575762229859 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (982305870627881 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000)))) (orderedInterval (-49941883 / 1000000000000) (-49941873 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks0_1 :
    compactCertificate295.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1507109816834663 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (870130258447727 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1544061412942843 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000)))) (orderedInterval (-10122733328 / 1000000000000) (-10122733256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1442662462349767 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1029552006133111 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1167402244301169 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000)))) (orderedInterval (2740296116 / 1000000000000) (2740296137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (973258283496161 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (859903209431381 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (249233466430719 / 800000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000)))) (orderedInterval (-4232668676 / 1000000000000) (-4232665263 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks0_2 :
    compactCertificate295.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (689392884586093 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (584405983080773 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (365694129372119 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000)))) (orderedInterval (-1731255329 / 1000000000000) (-1731252354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (196671519020073 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (534001432199219 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (729133302481363 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000)))) (orderedInterval (-3896922836 / 1000000000000) (-3896921121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (308305870627881 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1253246247472201 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (837110412787559 / 4000000000000) 0 (IntervalRat.scale (337 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000)))) (orderedInterval (-3686045276 / 1000000000000) (-3686044824 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks0 :
    compactCertificate295.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate295.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate295_chunkChecks0_0
    compactCertificate295_chunkChecks0_1 compactCertificate295_chunkChecks0_2

theorem compactCertificate295_chunkChecks1_0 :
    compactCertificate295.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (337 / 2) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (496465349442637 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (160546693485421 / 800000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000)))) (orderedInterval (26784349913 / 1000000000000) (26784350571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (144867350765159 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (389134081433723 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1056574728451791 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000)))) (orderedInterval (-4346515997 / 1000000000000) (-4346515868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (778268162867783 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1333575762229859 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (982305870627881 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000)))) (orderedInterval (-589896946 / 1000000000000) (-589896929 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks1_1 :
    compactCertificate295.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1507109816834663 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (870130258447727 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1544061412942843 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000)))) (orderedInterval (-26087693015 / 1000000000000) (-26087692870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1442662462349767 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1029552006133111 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1167402244301169 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000)))) (orderedInterval (8035748414 / 1000000000000) (8035748448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (973258283496161 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (859903209431381 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (249233466430719 / 800000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000)))) (orderedInterval (2074388603 / 1000000000000) (2074393122 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks1_2 :
    compactCertificate295.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (689392884586093 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (584405983080773 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (365694129372119 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000)))) (orderedInterval (11019712080 / 1000000000000) (11019714663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (196671519020073 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (534001432199219 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (729133302481363 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000)))) (orderedInterval (-2922694512 / 1000000000000) (-2922693158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (308305870627881 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1253246247472201 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (837110412787559 / 4000000000000) 1 (IntervalRat.scale (337 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000)))) (orderedInterval (4719660346 / 1000000000000) (4719660767 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks1 :
    compactCertificate295.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate295.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate295_chunkChecks1_0
    compactCertificate295_chunkChecks1_1 compactCertificate295_chunkChecks1_2

theorem compactCertificate295_chunkChecks2_0 :
    compactCertificate295.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (337 / 2) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (496465349442637 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (160546693485421 / 800000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000)))) (orderedInterval (6852046252 / 1000000000000) (6852046818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (144867350765159 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (389134081433723 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1056574728451791 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000)))) (orderedInterval (7974483787 / 1000000000000) (7974483843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (778268162867783 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1333575762229859 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (982305870627881 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000)))) (orderedInterval (2332059709 / 1000000000000) (2332059739 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks2_1 :
    compactCertificate295.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1507109816834663 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (870130258447727 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1544061412942843 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000)))) (orderedInterval (37948987674 / 1000000000000) (37948987980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1442662462349767 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1029552006133111 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1167402244301169 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000)))) (orderedInterval (-6797016095 / 1000000000000) (-6797016040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (973258283496161 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (859903209431381 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (249233466430719 / 800000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000)))) (orderedInterval (9098342985 / 1000000000000) (9098349018 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks2_2 :
    compactCertificate295.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (689392884586093 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (584405983080773 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (365694129372119 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000)))) (orderedInterval (-840359584 / 1000000000000) (-840357326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (196671519020073 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (534001432199219 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (729133302481363 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000)))) (orderedInterval (4671766726 / 1000000000000) (4671767808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (308305870627881 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1253246247472201 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (837110412787559 / 4000000000000) 2 (IntervalRat.scale (337 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000)))) (orderedInterval (5676777817 / 1000000000000) (5676778288 / 1000000000000))) = true
  rfl'

theorem compactCertificate295_chunkChecks2 :
    compactCertificate295.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate295.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate295_chunkChecks2_0
    compactCertificate295_chunkChecks2_1 compactCertificate295_chunkChecks2_2

theorem compactCertificate295_chunkChecks3_0 :
    compactCertificate295.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (337 / 2) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (496465349442637 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (160546693485421 / 800000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000)))) (orderedInterval (-28172538935 / 1000000000000) (-28172538440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (144867350765159 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (389134081433723 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1056574728451791 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000)))) (orderedInterval (7248314774 / 1000000000000) (7248314828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (778268162867783 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1333575762229859 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (982305870627881 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000)))) (orderedInterval (3095120238 / 1000000000000) (3095120292 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate295_chunkChecks3_1 :
    compactCertificate295.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1507109816834663 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (870130258447727 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1544061412942843 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000)))) (orderedInterval (132891165633 / 1000000000000) (132891166296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1442662462349767 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1029552006133111 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1167402244301169 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000)))) (orderedInterval (-22550822195 / 1000000000000) (-22550822102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (973258283496161 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (859903209431381 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (249233466430719 / 800000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000)))) (orderedInterval (-2674405934 / 1000000000000) (-2674397886 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate295_chunkChecks3_2 :
    compactCertificate295.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (689392884586093 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (584405983080773 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (365694129372119 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000)))) (orderedInterval (-11331609796 / 1000000000000) (-11331607835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (196671519020073 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (534001432199219 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (729133302481363 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000)))) (orderedInterval (3227092589 / 1000000000000) (3227093451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (308305870627881 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1253246247472201 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (837110412787559 / 4000000000000) 3 (IntervalRat.scale (337 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000)))) (orderedInterval (5465072447 / 1000000000000) (5465073030 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate295_chunkChecks3 :
    compactCertificate295.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate295.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate295_chunkChecks3_0
    compactCertificate295_chunkChecks3_1 compactCertificate295_chunkChecks3_2

theorem compactCertificate295_chunkChecks4_0 :
    compactCertificate295.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (337 / 2) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21730563703 / 1000000000000) (-21730563017 / 1000000000000), orderedInterval (57561907289 / 1000000000000) (57561907975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (496465349442637 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49493745615 / 1000000000000) (-49493691401 / 1000000000000), orderedInterval (51964125736 / 1000000000000) (51964179950 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (160546693485421 / 800000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (22254953724 / 1000000000000) (22254953725 / 1000000000000), orderedInterval (51684127035 / 1000000000000) (51684127036 / 1000000000000)))) (orderedInterval (-5786701298 / 1000000000000) (-5786700850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (144867350765159 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85440728255 / 1000000000000) (-85440683011 / 1000000000000), orderedInterval (102560654089 / 1000000000000) (102560699333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (389134081433723 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50756293571 / 1000000000000) (-50756293570 / 1000000000000), orderedInterval (-62729457217 / 1000000000000) (-62729457216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1056574728451791 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (42208813374 / 1000000000000) (42208813375 / 1000000000000), orderedInterval (24990819358 / 1000000000000) (24990819359 / 1000000000000)))) (orderedInterval (-18410208550 / 1000000000000) (-18410208474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (778268162867783 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31014399237 / 1000000000000) (31014399238 / 1000000000000), orderedInterval (47983727002 / 1000000000000) (47983727003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1333575762229859 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (40237333796 / 1000000000000) (40237333797 / 1000000000000), orderedInterval (16982765188 / 1000000000000) (16982765189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (982305870627881 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49285714793 / 1000000000000) (49285714795 / 1000000000000), orderedInterval (12677057674 / 1000000000000) (12677057676 / 1000000000000)))) (orderedInterval (-13683408362 / 1000000000000) (-13683408262 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate295_chunkChecks4_1 :
    compactCertificate295.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1507109816834663 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22230219400 / 1000000000000) (22230219401 / 1000000000000), orderedInterval (34545953061 / 1000000000000) (34545953062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (870130258447727 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54082833562 / 1000000000000) (-54082833506 / 1000000000000), orderedInterval (-1136121075 / 1000000000000) (-1136121019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1544061412942843 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15233971411 / 1000000000000) (-15233971410 / 1000000000000), orderedInterval (-37625128343 / 1000000000000) (-37625128342 / 1000000000000)))) (orderedInterval (-171105966000 / 1000000000000) (-171105964536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1442662462349767 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7004876032 / 1000000000000) (-7004876031 / 1000000000000), orderedInterval (-41415619086 / 1000000000000) (-41415619085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1029552006133111 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26515071343 / 1000000000000) (26515071344 / 1000000000000), orderedInterval (42023883941 / 1000000000000) (42023883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1167402244301169 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21044118045 / 1000000000000) (-21044118044 / 1000000000000), orderedInterval (-41658887513 / 1000000000000) (-41658887512 / 1000000000000)))) (orderedInterval (17531391956 / 1000000000000) (17531392116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (973258283496161 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41451062354 / 1000000000000) (-41450978295 / 1000000000000), orderedInterval (30056095959 / 1000000000000) (30056180018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (859903209431381 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46062073258 / 1000000000000) (46062115631 / 1000000000000), orderedInterval (-29083615912 / 1000000000000) (-29083573539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (249233466430719 / 800000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43666061879 / 1000000000000) (-43666061876 / 1000000000000), orderedInterval (-11622717408 / 1000000000000) (-11622717405 / 1000000000000)))) (orderedInterval (-22098257680 / 1000000000000) (-22098246854 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate295_chunkChecks4_2 :
    compactCertificate295.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (689392884586093 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20571462101 / 1000000000000) (-20571462100 / 1000000000000), orderedInterval (-57129711406 / 1000000000000) (-57129711405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (584405983080773 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45895916993 / 1000000000000) (45895968807 / 1000000000000), orderedInterval (-47601199903 / 1000000000000) (-47601148088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (365694129372119 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74420108607 / 1000000000000) (-74420108606 / 1000000000000), orderedInterval (-37342156793 / 1000000000000) (-37342156792 / 1000000000000)))) (orderedInterval (2056372480 / 1000000000000) (2056374196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (196671519020073 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-35225270133 / 1000000000000) (-35225269337 / 1000000000000), orderedInterval (108559842657 / 1000000000000) (108559843452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (534001432199219 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49713192205 / 1000000000000) (49713266232 / 1000000000000), orderedInterval (-48116048604 / 1000000000000) (-48115974576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (729133302481363 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44618658057 / 1000000000000) (44618658058 / 1000000000000), orderedInterval (38628709428 / 1000000000000) (38628709429 / 1000000000000)))) (orderedInterval (-5161145024 / 1000000000000) (-5161144332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (308305870627881 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57115278149 / 1000000000000) (57115309811 / 1000000000000), orderedInterval (-71063270073 / 1000000000000) (-71063238411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1253246247472201 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2824647069 / 1000000000000) (-2824647066 / 1000000000000), orderedInterval (44992621153 / 1000000000000) (44992621157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (837110412787559 / 4000000000000) 4 (IntervalRat.scale (337 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22706202731 / 1000000000000) (22706203872 / 1000000000000), orderedInterval (-50317766676 / 1000000000000) (-50317765534 / 1000000000000)))) (orderedInterval (-7438524610 / 1000000000000) (-7438523844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate295_chunkChecks4 :
    compactCertificate295.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate295.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate295_chunkChecks4_0
    compactCertificate295_chunkChecks4_1 compactCertificate295_chunkChecks4_2

theorem compactCertificate295_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate295.chunkCheck r b = true :=
  compactCertificate295.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate295_chunkChecks0
    · exact compactCertificate295_chunkChecks1
    · exact compactCertificate295_chunkChecks2
    · exact compactCertificate295_chunkChecks3
    · exact compactCertificate295_chunkChecks4)

theorem compactCertificate295_coefficient0 :
    compactCertificate295.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate295_coefficient1 :
    compactCertificate295.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate295_coefficient2 :
    compactCertificate295.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate295_coefficient3 :
    compactCertificate295.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate295_coefficient4 :
    compactCertificate295.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate295_coefficients : ∀ r : Fin 5,
    compactCertificate295.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate295_coefficient0
  · exact compactCertificate295_coefficient1
  · exact compactCertificate295_coefficient2
  · exact compactCertificate295_coefficient3
  · exact compactCertificate295_coefficient4

theorem compactCertificate295_lower : (1 : ℚ) ≤ compactCertificate295.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate295, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate295_proves {t : ℝ} (ht : t ∈ compactCertificate295.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate295.proves compactCertificate295_states compactCertificate295_chunks
    compactCertificate295_coefficients compactCertificate295_lower ht

end Erdos232
