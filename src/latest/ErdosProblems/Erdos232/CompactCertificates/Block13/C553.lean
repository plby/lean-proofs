/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate553 : CompactCertificate where
  left := 424
  right := 425
  center := 849 / 2
  grid := fun i =>
    match i.val with
    | 0 => 135
    | 1 => 100
    | 2 => 161
    | 3 => 29
    | 4 => 78
    | 5 => 212
    | 6 => 156
    | 7 => 267
    | 8 => 197
    | 9 => 302
    | 10 => 175
    | 11 => 310
    | 12 => 289
    | 13 => 207
    | 14 => 234
    | 15 => 195
    | 16 => 172
    | 17 => 250
    | 18 => 138
    | 19 => 117
    | 20 => 73
    | 21 => 39
    | 22 => 107
    | 23 => 146
    | 24 => 62
    | 25 => 251
    | _ => 168
  point := fun i =>
    match i.val with
    | 0 => 849 / 2
    | 1 => 1250739114767949 / 4000000000000
    | 2 => 404463331659117 / 800000000000
    | 3 => 364962554301543 / 4000000000000
    | 4 => 980340757083771 / 4000000000000
    | 5 => 2661815858918607 / 4000000000000
    | 6 => 1960681514168391 / 4000000000000
    | 7 => 3359661193273443 / 4000000000000
    | 8 => 2474711228970537 / 4000000000000
    | 9 => 3796843425794151 / 4000000000000
    | 10 => 2192108573952879 / 4000000000000
    | 11 => 3889935132310011 / 4000000000000
    | 12 => 3634481989717959 / 4000000000000
    | 13 => 2593737843344247 / 4000000000000
    | 14 => 2941022271251313 / 4000000000000
    | 15 => 2451917752784097 / 4000000000000
    | 16 => 2166343693790037 / 4000000000000
    | 17 => 627890839761663 / 800000000000
    | 18 => 1736779106865261 / 4000000000000
    | 19 => 1472286883191621 / 4000000000000
    | 20 => 921288771029463 / 4000000000000
    | 21 => 495472165127721 / 4000000000000
    | 22 => 1345303311386163 / 4000000000000
    | 23 => 1836896658180051 / 4000000000000
    | 24 => 776711228970537 / 4000000000000
    | 25 => 3157288024047177 / 4000000000000
    | _ => 2108922078506343 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))
    | 1 => (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))
    | 2 => (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000))
    | 3 => (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))
    | 4 => (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
    | 5 => (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000))
    | 6 => (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))
    | 7 => (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))
    | 8 => (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000))
    | 9 => (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))
    | 10 => (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))
    | 11 => (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000))
    | 12 => (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))
    | 13 => (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))
    | 14 => (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000))
    | 15 => (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))
    | 16 => (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))
    | 17 => (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000))
    | 18 => (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))
    | 19 => (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))
    | 20 => (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000))
    | 21 => (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))
    | 22 => (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))
    | 23 => (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000))
    | 24 => (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))
    | 25 => (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))
    | _ => (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15521157009 / 1000000000000) (-15521156873 / 1000000000000)
      | 1 => orderedInterval (1605002799 / 1000000000000) (1605002850 / 1000000000000)
      | 2 => orderedInterval (386976765 / 1000000000000) (386979398 / 1000000000000)
      | 3 => orderedInterval (-4394098443 / 1000000000000) (-4394094584 / 1000000000000)
      | 4 => orderedInterval (2985794045 / 1000000000000) (2985802856 / 1000000000000)
      | 5 => orderedInterval (-1929244103 / 1000000000000) (-1929240297 / 1000000000000)
      | 6 => orderedInterval (-5485684350 / 1000000000000) (-5485684197 / 1000000000000)
      | 7 => orderedInterval (-844977039 / 1000000000000) (-844976480 / 1000000000000)
      | _ => orderedInterval (900463475 / 1000000000000) (900463823 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7820821291 / 1000000000000) (-7820821179 / 1000000000000)
      | 1 => orderedInterval (-2517955861 / 1000000000000) (-2517955802 / 1000000000000)
      | 2 => orderedInterval (-1487884321 / 1000000000000) (-1487879117 / 1000000000000)
      | 3 => orderedInterval (1522124055 / 1000000000000) (1522129204 / 1000000000000)
      | 4 => orderedInterval (-2168209462 / 1000000000000) (-2168195974 / 1000000000000)
      | 5 => orderedInterval (2171456324 / 1000000000000) (2171461187 / 1000000000000)
      | 6 => orderedInterval (-60434247 / 1000000000000) (-60434119 / 1000000000000)
      | 7 => orderedInterval (-471672985 / 1000000000000) (-471672790 / 1000000000000)
      | _ => orderedInterval (-7719454488 / 1000000000000) (-7719453895 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15885927545 / 1000000000000) (15885927641 / 1000000000000)
      | 1 => orderedInterval (703937160 / 1000000000000) (703937240 / 1000000000000)
      | 2 => orderedInterval (-2259763284 / 1000000000000) (-2259752985 / 1000000000000)
      | 3 => orderedInterval (29421195575 / 1000000000000) (29421202612 / 1000000000000)
      | 4 => orderedInterval (-7953914925 / 1000000000000) (-7953894227 / 1000000000000)
      | 5 => orderedInterval (2966946252 / 1000000000000) (2966952480 / 1000000000000)
      | 6 => orderedInterval (5144026305 / 1000000000000) (5144026420 / 1000000000000)
      | 7 => orderedInterval (2646254215 / 1000000000000) (2646254306 / 1000000000000)
      | _ => orderedInterval (-5713424404 / 1000000000000) (-5713423363 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8767183687 / 1000000000000) (8767183775 / 1000000000000)
      | 1 => orderedInterval (8012744257 / 1000000000000) (8012744377 / 1000000000000)
      | 2 => orderedInterval (4126738865 / 1000000000000) (4126759231 / 1000000000000)
      | 3 => orderedInterval (-15541550022 / 1000000000000) (-15541540078 / 1000000000000)
      | 4 => orderedInterval (4988857583 / 1000000000000) (4988889336 / 1000000000000)
      | 5 => orderedInterval (-5780749028 / 1000000000000) (-5780741059 / 1000000000000)
      | 6 => orderedInterval (356758736 / 1000000000000) (356758844 / 1000000000000)
      | 7 => orderedInterval (564516381 / 1000000000000) (564516442 / 1000000000000)
      | _ => orderedInterval (12106110263 / 1000000000000) (12106112119 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16507170977 / 1000000000000) (-16507170893 / 1000000000000)
      | 1 => orderedInterval (-2801829152 / 1000000000000) (-2801828967 / 1000000000000)
      | 2 => orderedInterval (10430329939 / 1000000000000) (10430370264 / 1000000000000)
      | 3 => orderedInterval (-161365160105 / 1000000000000) (-161365145308 / 1000000000000)
      | 4 => orderedInterval (23216779135 / 1000000000000) (23216828001 / 1000000000000)
      | 5 => orderedInterval (-4027907141 / 1000000000000) (-4027896914 / 1000000000000)
      | 6 => orderedInterval (-5512547577 / 1000000000000) (-5512547474 / 1000000000000)
      | 7 => orderedInterval (-3477364087 / 1000000000000) (-3477364032 / 1000000000000)
      | _ => orderedInterval (24071746379 / 1000000000000) (24071749739 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-22296923860 / 1000000000000) (-22296903504 / 1000000000000)
    | 1 => orderedInterval (-18552852276 / 1000000000000) (-18552822485 / 1000000000000)
    | 2 => orderedInterval (40841184439 / 1000000000000) (40841230124 / 1000000000000)
    | 3 => orderedInterval (17600610722 / 1000000000000) (17600682987 / 1000000000000)
    | _ => orderedInterval (-135973123586 / 1000000000000) (-135973005584 / 1000000000000)

theorem compactCertificate553_stateChecks0 :
    compactCertificate553.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (849 / 2)) (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250739114767949 / 4000000000000)) (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (404463331659117 / 800000000000)) (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks1 :
    compactCertificate553.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (364962554301543 / 4000000000000)) (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (980340757083771 / 4000000000000)) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2661815858918607 / 4000000000000)) (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks2 :
    compactCertificate553.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1960681514168391 / 4000000000000)) (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3359661193273443 / 4000000000000)) (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2474711228970537 / 4000000000000)) (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks3 :
    compactCertificate553.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3796843425794151 / 4000000000000)) (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2192108573952879 / 4000000000000)) (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 310 12 (3889935132310011 / 4000000000000)) (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks4 :
    compactCertificate553.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3634481989717959 / 4000000000000)) (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2593737843344247 / 4000000000000)) (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2941022271251313 / 4000000000000)) (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks5 :
    compactCertificate553.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2451917752784097 / 4000000000000)) (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2166343693790037 / 4000000000000)) (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (627890839761663 / 800000000000)) (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks6 :
    compactCertificate553.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1736779106865261 / 4000000000000)) (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1472286883191621 / 4000000000000)) (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (921288771029463 / 4000000000000)) (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks7 :
    compactCertificate553.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (495472165127721 / 4000000000000)) (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1345303311386163 / 4000000000000)) (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1836896658180051 / 4000000000000)) (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_stateChecks8 :
    compactCertificate553.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (776711228970537 / 4000000000000)) (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3157288024047177 / 4000000000000)) (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2108922078506343 / 4000000000000)) (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_states : ∀ j,
    BesselStateValid (compactCertificate553.point j) (compactCertificate553.state j) :=
  compactCertificate553.statesValid_of_checks3 compactCertificate553_stateChecks0
    compactCertificate553_stateChecks1 compactCertificate553_stateChecks2
    compactCertificate553_stateChecks3 compactCertificate553_stateChecks4
    compactCertificate553_stateChecks5 compactCertificate553_stateChecks6
    compactCertificate553_stateChecks7 compactCertificate553_stateChecks8

theorem compactCertificate553_chunkChecks0_0 :
    compactCertificate553.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (849 / 2) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1250739114767949 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (404463331659117 / 800000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000)))) (orderedInterval (-15521157009 / 1000000000000) (-15521156873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (364962554301543 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2661815858918607 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000)))) (orderedInterval (1605002799 / 1000000000000) (1605002850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1960681514168391 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3359661193273443 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2474711228970537 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000)))) (orderedInterval (386976765 / 1000000000000) (386979398 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks0_1 :
    compactCertificate553.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3796843425794151 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2192108573952879 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3889935132310011 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000)))) (orderedInterval (-4394098443 / 1000000000000) (-4394094584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3634481989717959 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2593737843344247 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2941022271251313 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000)))) (orderedInterval (2985794045 / 1000000000000) (2985802856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2451917752784097 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2166343693790037 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (627890839761663 / 800000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000)))) (orderedInterval (-1929244103 / 1000000000000) (-1929240297 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks0_2 :
    compactCertificate553.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1736779106865261 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1472286883191621 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (921288771029463 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000)))) (orderedInterval (-5485684350 / 1000000000000) (-5485684197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (495472165127721 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1345303311386163 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1836896658180051 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000)))) (orderedInterval (-844977039 / 1000000000000) (-844976480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (776711228970537 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3157288024047177 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2108922078506343 / 4000000000000) 0 (IntervalRat.scale (849 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000)))) (orderedInterval (900463475 / 1000000000000) (900463823 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks0 :
    compactCertificate553.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate553.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate553_chunkChecks0_0
    compactCertificate553_chunkChecks0_1 compactCertificate553_chunkChecks0_2

theorem compactCertificate553_chunkChecks1_0 :
    compactCertificate553.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (849 / 2) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1250739114767949 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (404463331659117 / 800000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000)))) (orderedInterval (-7820821291 / 1000000000000) (-7820821179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (364962554301543 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2661815858918607 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000)))) (orderedInterval (-2517955861 / 1000000000000) (-2517955802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1960681514168391 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3359661193273443 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2474711228970537 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000)))) (orderedInterval (-1487884321 / 1000000000000) (-1487879117 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks1_1 :
    compactCertificate553.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3796843425794151 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2192108573952879 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3889935132310011 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000)))) (orderedInterval (1522124055 / 1000000000000) (1522129204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3634481989717959 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2593737843344247 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2941022271251313 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000)))) (orderedInterval (-2168209462 / 1000000000000) (-2168195974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2451917752784097 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2166343693790037 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (627890839761663 / 800000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000)))) (orderedInterval (2171456324 / 1000000000000) (2171461187 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks1_2 :
    compactCertificate553.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1736779106865261 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1472286883191621 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (921288771029463 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000)))) (orderedInterval (-60434247 / 1000000000000) (-60434119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (495472165127721 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1345303311386163 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1836896658180051 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000)))) (orderedInterval (-471672985 / 1000000000000) (-471672790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (776711228970537 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3157288024047177 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2108922078506343 / 4000000000000) 1 (IntervalRat.scale (849 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000)))) (orderedInterval (-7719454488 / 1000000000000) (-7719453895 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks1 :
    compactCertificate553.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate553.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate553_chunkChecks1_0
    compactCertificate553_chunkChecks1_1 compactCertificate553_chunkChecks1_2

theorem compactCertificate553_chunkChecks2_0 :
    compactCertificate553.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (849 / 2) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1250739114767949 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (404463331659117 / 800000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000)))) (orderedInterval (15885927545 / 1000000000000) (15885927641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (364962554301543 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2661815858918607 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000)))) (orderedInterval (703937160 / 1000000000000) (703937240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1960681514168391 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3359661193273443 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2474711228970537 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000)))) (orderedInterval (-2259763284 / 1000000000000) (-2259752985 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks2_1 :
    compactCertificate553.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3796843425794151 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2192108573952879 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3889935132310011 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000)))) (orderedInterval (29421195575 / 1000000000000) (29421202612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3634481989717959 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2593737843344247 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2941022271251313 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000)))) (orderedInterval (-7953914925 / 1000000000000) (-7953894227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2451917752784097 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2166343693790037 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (627890839761663 / 800000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000)))) (orderedInterval (2966946252 / 1000000000000) (2966952480 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks2_2 :
    compactCertificate553.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1736779106865261 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1472286883191621 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (921288771029463 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000)))) (orderedInterval (5144026305 / 1000000000000) (5144026420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (495472165127721 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1345303311386163 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1836896658180051 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000)))) (orderedInterval (2646254215 / 1000000000000) (2646254306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (776711228970537 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3157288024047177 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2108922078506343 / 4000000000000) 2 (IntervalRat.scale (849 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000)))) (orderedInterval (-5713424404 / 1000000000000) (-5713423363 / 1000000000000))) = true
  rfl'

theorem compactCertificate553_chunkChecks2 :
    compactCertificate553.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate553.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate553_chunkChecks2_0
    compactCertificate553_chunkChecks2_1 compactCertificate553_chunkChecks2_2

theorem compactCertificate553_chunkChecks3_0 :
    compactCertificate553.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (849 / 2) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1250739114767949 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (404463331659117 / 800000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000)))) (orderedInterval (8767183687 / 1000000000000) (8767183775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (364962554301543 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2661815858918607 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000)))) (orderedInterval (8012744257 / 1000000000000) (8012744377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1960681514168391 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3359661193273443 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2474711228970537 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000)))) (orderedInterval (4126738865 / 1000000000000) (4126759231 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate553_chunkChecks3_1 :
    compactCertificate553.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3796843425794151 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2192108573952879 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3889935132310011 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000)))) (orderedInterval (-15541550022 / 1000000000000) (-15541540078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3634481989717959 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2593737843344247 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2941022271251313 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000)))) (orderedInterval (4988857583 / 1000000000000) (4988889336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2451917752784097 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2166343693790037 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (627890839761663 / 800000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000)))) (orderedInterval (-5780749028 / 1000000000000) (-5780741059 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate553_chunkChecks3_2 :
    compactCertificate553.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1736779106865261 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1472286883191621 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (921288771029463 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000)))) (orderedInterval (356758736 / 1000000000000) (356758844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (495472165127721 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1345303311386163 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1836896658180051 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000)))) (orderedInterval (564516381 / 1000000000000) (564516442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (776711228970537 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3157288024047177 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2108922078506343 / 4000000000000) 3 (IntervalRat.scale (849 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000)))) (orderedInterval (12106110263 / 1000000000000) (12106112119 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate553_chunkChecks3 :
    compactCertificate553.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate553.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate553_chunkChecks3_0
    compactCertificate553_chunkChecks3_1 compactCertificate553_chunkChecks3_2

theorem compactCertificate553_chunkChecks4_0 :
    compactCertificate553.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (849 / 2) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35658300349 / 1000000000000) (-35658300348 / 1000000000000), orderedInterval (-15063565357 / 1000000000000) (-15063565355 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1250739114767949 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28703896560 / 1000000000000) (-28703885241 / 1000000000000), orderedInterval (34860639256 / 1000000000000) (34860650574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (404463331659117 / 800000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19086036769 / 1000000000000) (-19086036768 / 1000000000000), orderedInterval (-29896213741 / 1000000000000) (-29896213740 / 1000000000000)))) (orderedInterval (-16507170977 / 1000000000000) (-16507170893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (364962554301543 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66379626285 / 1000000000000) (-66379626284 / 1000000000000), orderedInterval (-50342151825 / 1000000000000) (-50342151824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (980340757083771 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37466404890 / 1000000000000) (37466404891 / 1000000000000), orderedInterval (34475162817 / 1000000000000) (34475162818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2661815858918607 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6796108541 / 1000000000000) (6796108542 / 1000000000000), orderedInterval (30169105210 / 1000000000000) (30169105211 / 1000000000000)))) (orderedInterval (-2801829152 / 1000000000000) (-2801828967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1960681514168391 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27476990035 / 1000000000000) (27476990036 / 1000000000000), orderedInterval (23291220218 / 1000000000000) (23291220219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3359661193273443 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26094110511 / 1000000000000) (-26094025932 / 1000000000000), orderedInterval (8793677135 / 1000000000000) (8793761713 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2474711228970537 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17290090941 / 1000000000000) (-17290090940 / 1000000000000), orderedInterval (-27005526863 / 1000000000000) (-27005526862 / 1000000000000)))) (orderedInterval (10430329939 / 1000000000000) (10430370264 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate553_chunkChecks4_1 :
    compactCertificate553.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3796843425794151 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24452332996 / 1000000000000) (24452333124 / 1000000000000), orderedInterval (8517449748 / 1000000000000) (8517449876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2192108573952879 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28045099017 / 1000000000000) (28045148317 / 1000000000000), orderedInterval (-19393838158 / 1000000000000) (-19393788858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3889935132310011 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14963326697 / 1000000000000) (-14963326593 / 1000000000000), orderedInterval (20761769364 / 1000000000000) (20761769468 / 1000000000000)))) (orderedInterval (-161365160105 / 1000000000000) (-161365145308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3634481989717959 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26373411725 / 1000000000000) (-26373409500 / 1000000000000), orderedInterval (-2241016269 / 1000000000000) (-2241014044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2593737843344247 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27781141204 / 1000000000000) (27781233417 / 1000000000000), orderedInterval (-14512328659 / 1000000000000) (-14512236446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2941022271251313 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23197298572 / 1000000000000) (23197298573 / 1000000000000), orderedInterval (18087638374 / 1000000000000) (18087638375 / 1000000000000)))) (orderedInterval (23216779135 / 1000000000000) (23216828001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2451917752784097 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29468720217 / 1000000000000) (-29468720213 / 1000000000000), orderedInterval (-13020523768 / 1000000000000) (-13020523765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2166343693790037 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30926053450 / 1000000000000) (30926119245 / 1000000000000), orderedInterval (-14828924003 / 1000000000000) (-14828858208 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (627890839761663 / 800000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7063363690 / 1000000000000) (7063363691 / 1000000000000), orderedInterval (27585908563 / 1000000000000) (27585908564 / 1000000000000)))) (orderedInterval (-4027907141 / 1000000000000) (-4027896914 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate553_chunkChecks4_2 :
    compactCertificate553.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1736779106865261 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37964514469 / 1000000000000) (37964514526 / 1000000000000), orderedInterval (4946523113 / 1000000000000) (4946523171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1472286883191621 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39964778234 / 1000000000000) (-39964778231 / 1000000000000), orderedInterval (-11453234063 / 1000000000000) (-11453234060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (921288771029463 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51526219806 / 1000000000000) (-51526218667 / 1000000000000), orderedInterval (10556127412 / 1000000000000) (10556128551 / 1000000000000)))) (orderedInterval (-5512547577 / 1000000000000) (-5512547474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (495472165127721 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-60757994605 / 1000000000000) (-60757967141 / 1000000000000), orderedInterval (38297162035 / 1000000000000) (38297189499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1345303311386163 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35651600482 / 1000000000000) (-35651600481 / 1000000000000), orderedInterval (-24883494045 / 1000000000000) (-24883494044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1836896658180051 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36217952122 / 1000000000000) (36217952137 / 1000000000000), orderedInterval (8594994902 / 1000000000000) (8594994917 / 1000000000000)))) (orderedInterval (-3477364087 / 1000000000000) (-3477364032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (776711228970537 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (10465912705 / 1000000000000) (10465912706 / 1000000000000), orderedInterval (56267057167 / 1000000000000) (56267057168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3157288024047177 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28399491198 / 1000000000000) (-28399488373 / 1000000000000), orderedInterval (-75916794 / 1000000000000) (-75913970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2108922078506343 / 4000000000000) 4 (IntervalRat.scale (849 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7858149182 / 1000000000000) (7858149183 / 1000000000000), orderedInterval (33841166052 / 1000000000000) (33841166053 / 1000000000000)))) (orderedInterval (24071746379 / 1000000000000) (24071749739 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate553_chunkChecks4 :
    compactCertificate553.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate553.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate553_chunkChecks4_0
    compactCertificate553_chunkChecks4_1 compactCertificate553_chunkChecks4_2

theorem compactCertificate553_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate553.chunkCheck r b = true :=
  compactCertificate553.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate553_chunkChecks0
    · exact compactCertificate553_chunkChecks1
    · exact compactCertificate553_chunkChecks2
    · exact compactCertificate553_chunkChecks3
    · exact compactCertificate553_chunkChecks4)

theorem compactCertificate553_coefficient0 :
    compactCertificate553.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate553_coefficient1 :
    compactCertificate553.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate553_coefficient2 :
    compactCertificate553.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate553_coefficient3 :
    compactCertificate553.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate553_coefficient4 :
    compactCertificate553.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate553_coefficients : ∀ r : Fin 5,
    compactCertificate553.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate553_coefficient0
  · exact compactCertificate553_coefficient1
  · exact compactCertificate553_coefficient2
  · exact compactCertificate553_coefficient3
  · exact compactCertificate553_coefficient4

theorem compactCertificate553_lower : (1 : ℚ) ≤ compactCertificate553.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate553, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate553_proves {t : ℝ} (ht : t ∈ compactCertificate553.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate553.proves compactCertificate553_states compactCertificate553_chunks
    compactCertificate553_coefficients compactCertificate553_lower ht

end Erdos232
