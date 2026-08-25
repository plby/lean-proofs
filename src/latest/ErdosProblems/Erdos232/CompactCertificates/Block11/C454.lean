/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate454 : CompactCertificate where
  left := 325
  right := 326
  center := 651 / 2
  grid := fun i =>
    match i.val with
    | 0 => 104
    | 1 => 76
    | 2 => 123
    | 3 => 22
    | 4 => 60
    | 5 => 163
    | 6 => 120
    | 7 => 205
    | 8 => 151
    | 9 => 232
    | 10 => 134
    | 11 => 237
    | 12 => 222
    | 13 => 158
    | 14 => 180
    | 15 => 150
    | 16 => 132
    | 17 => 192
    | 18 => 106
    | 19 => 90
    | 20 => 56
    | 21 => 30
    | 22 => 82
    | 23 => 112
    | 24 => 47
    | 25 => 193
    | _ => 129
  point := fun i =>
    match i.val with
    | 0 => 651 / 2
    | 1 => 959047307083551 / 4000000000000
    | 2 => 310136194240383 / 800000000000
    | 3 => 279847612308957 / 4000000000000
    | 4 => 751710050484729 / 4000000000000
    | 5 => 2041039015495893 / 4000000000000
    | 6 => 1503420100970109 / 4000000000000
    | 7 => 2576135967987057 / 4000000000000
    | 8 => 1897570094298963 / 4000000000000
    | 9 => 2911360506704349 / 4000000000000
    | 10 => 1680874772253621 / 4000000000000
    | 11 => 2982741779898489 / 4000000000000
    | 12 => 2786864281868541 / 4000000000000
    | 13 => 1988837851610253 / 4000000000000
    | 14 => 2255130151454187 / 4000000000000
    | 15 => 1880092411145403 / 4000000000000
    | 16 => 1661118662729463 / 4000000000000
    | 17 => 481456933668837 / 800000000000
    | 18 => 1331735216218239 / 4000000000000
    | 19 => 1128926691351879 / 4000000000000
    | 20 => 706429905701037 / 4000000000000
    | 21 => 379920352765779 / 4000000000000
    | 22 => 1031557662794337 / 4000000000000
    | 23 => 1408503797968449 / 4000000000000
    | 24 => 595570094298963 / 4000000000000
    | 25 => 2420959368262323 / 4000000000000
    | _ => 1617088660904157 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))
    | 1 => (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))
    | 2 => (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000))
    | 3 => (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))
    | 4 => (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
    | 5 => (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000))
    | 6 => (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))
    | 7 => (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))
    | 8 => (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000))
    | 9 => (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))
    | 10 => (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))
    | 11 => (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000))
    | 12 => (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))
    | 13 => (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))
    | 14 => (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000))
    | 15 => (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))
    | 16 => (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))
    | 17 => (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000))
    | 18 => (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))
    | 19 => (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))
    | 20 => (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000))
    | 21 => (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))
    | 22 => (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))
    | 23 => (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000))
    | 24 => (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))
    | 25 => (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))
    | _ => (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9128694548 / 1000000000000) (-9128691874 / 1000000000000)
      | 1 => orderedInterval (-2734937868 / 1000000000000) (-2734930413 / 1000000000000)
      | 2 => orderedInterval (57343855 / 1000000000000) (57343874 / 1000000000000)
      | 3 => orderedInterval (-2656844754 / 1000000000000) (-2656835310 / 1000000000000)
      | 4 => orderedInterval (3477348009 / 1000000000000) (3477348293 / 1000000000000)
      | 5 => orderedInterval (-2830994143 / 1000000000000) (-2830994090 / 1000000000000)
      | 6 => orderedInterval (-3339808027 / 1000000000000) (-3339807945 / 1000000000000)
      | 7 => orderedInterval (-5325722758 / 1000000000000) (-5325722718 / 1000000000000)
      | _ => orderedInterval (-2679778143 / 1000000000000) (-2679777982 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17072645057 / 1000000000000) (17072648182 / 1000000000000)
      | 1 => orderedInterval (3226323010 / 1000000000000) (3226334678 / 1000000000000)
      | 2 => orderedInterval (445117716 / 1000000000000) (445117748 / 1000000000000)
      | 3 => orderedInterval (-4536405265 / 1000000000000) (-4536383658 / 1000000000000)
      | 4 => orderedInterval (-1618963392 / 1000000000000) (-1618962925 / 1000000000000)
      | 5 => orderedInterval (1292905879 / 1000000000000) (1292905962 / 1000000000000)
      | 6 => orderedInterval (-7548453768 / 1000000000000) (-7548453692 / 1000000000000)
      | 7 => orderedInterval (-2195537366 / 1000000000000) (-2195537330 / 1000000000000)
      | _ => orderedInterval (13816755025 / 1000000000000) (13816755188 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10178670287 / 1000000000000) (10178673962 / 1000000000000)
      | 1 => orderedInterval (5190464529 / 1000000000000) (5190482846 / 1000000000000)
      | 2 => orderedInterval (-1360051927 / 1000000000000) (-1360051870 / 1000000000000)
      | 3 => orderedInterval (14561116855 / 1000000000000) (14561166381 / 1000000000000)
      | 4 => orderedInterval (-8115944152 / 1000000000000) (-8115943375 / 1000000000000)
      | 5 => orderedInterval (5501779234 / 1000000000000) (5501779369 / 1000000000000)
      | 6 => orderedInterval (4764657501 / 1000000000000) (4764657574 / 1000000000000)
      | 7 => orderedInterval (4066748834 / 1000000000000) (4066748870 / 1000000000000)
      | _ => orderedInterval (5123653880 / 1000000000000) (5123654090 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17675255890 / 1000000000000) (-17675251570 / 1000000000000)
      | 1 => orderedInterval (-5364912646 / 1000000000000) (-5364883936 / 1000000000000)
      | 2 => orderedInterval (-3351189925 / 1000000000000) (-3351189822 / 1000000000000)
      | 3 => orderedInterval (34246622823 / 1000000000000) (34246736222 / 1000000000000)
      | 4 => orderedInterval (6541649277 / 1000000000000) (6541650574 / 1000000000000)
      | 5 => orderedInterval (-4684986676 / 1000000000000) (-4684986452 / 1000000000000)
      | 6 => orderedInterval (7305653779 / 1000000000000) (7305653850 / 1000000000000)
      | 7 => orderedInterval (2298907298 / 1000000000000) (2298907334 / 1000000000000)
      | _ => orderedInterval (-30199170022 / 1000000000000) (-30199169715 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11498245135 / 1000000000000) (-11498240032 / 1000000000000)
      | 1 => orderedInterval (-12954987604 / 1000000000000) (-12954942512 / 1000000000000)
      | 2 => orderedInterval (7748758661 / 1000000000000) (7748758852 / 1000000000000)
      | 3 => orderedInterval (-78529212804 / 1000000000000) (-78528952762 / 1000000000000)
      | 4 => orderedInterval (18798553439 / 1000000000000) (18798555621 / 1000000000000)
      | 5 => orderedInterval (-11893499391 / 1000000000000) (-11893499009 / 1000000000000)
      | 6 => orderedInterval (-5274862993 / 1000000000000) (-5274862924 / 1000000000000)
      | 7 => orderedInterval (-4290407943 / 1000000000000) (-4290407904 / 1000000000000)
      | _ => orderedInterval (-12888916109 / 1000000000000) (-12888915623 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-25162088377 / 1000000000000) (-25162068165 / 1000000000000)
    | 1 => orderedInterval (19954386896 / 1000000000000) (19954424153 / 1000000000000)
    | 2 => orderedInterval (39911095041 / 1000000000000) (39911167847 / 1000000000000)
    | 3 => orderedInterval (-10882681982 / 1000000000000) (-10882533515 / 1000000000000)
    | _ => orderedInterval (-110782819879 / 1000000000000) (-110782506293 / 1000000000000)

theorem compactCertificate454_stateChecks0 :
    compactCertificate454.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (651 / 2)) (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (959047307083551 / 4000000000000)) (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (310136194240383 / 800000000000)) (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks1 :
    compactCertificate454.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (279847612308957 / 4000000000000)) (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (751710050484729 / 4000000000000)) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2041039015495893 / 4000000000000)) (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks2 :
    compactCertificate454.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1503420100970109 / 4000000000000)) (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2576135967987057 / 4000000000000)) (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1897570094298963 / 4000000000000)) (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks3 :
    compactCertificate454.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2911360506704349 / 4000000000000)) (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1680874772253621 / 4000000000000)) (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2982741779898489 / 4000000000000)) (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks4 :
    compactCertificate454.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2786864281868541 / 4000000000000)) (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1988837851610253 / 4000000000000)) (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2255130151454187 / 4000000000000)) (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks5 :
    compactCertificate454.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1880092411145403 / 4000000000000)) (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1661118662729463 / 4000000000000)) (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (481456933668837 / 800000000000)) (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks6 :
    compactCertificate454.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1331735216218239 / 4000000000000)) (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1128926691351879 / 4000000000000)) (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (706429905701037 / 4000000000000)) (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks7 :
    compactCertificate454.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (379920352765779 / 4000000000000)) (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1031557662794337 / 4000000000000)) (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1408503797968449 / 4000000000000)) (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_stateChecks8 :
    compactCertificate454.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (595570094298963 / 4000000000000)) (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2420959368262323 / 4000000000000)) (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1617088660904157 / 4000000000000)) (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_states : ∀ j,
    BesselStateValid (compactCertificate454.point j) (compactCertificate454.state j) :=
  compactCertificate454.statesValid_of_checks3 compactCertificate454_stateChecks0
    compactCertificate454_stateChecks1 compactCertificate454_stateChecks2
    compactCertificate454_stateChecks3 compactCertificate454_stateChecks4
    compactCertificate454_stateChecks5 compactCertificate454_stateChecks6
    compactCertificate454_stateChecks7 compactCertificate454_stateChecks8

theorem compactCertificate454_chunkChecks0_0 :
    compactCertificate454.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (651 / 2) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (959047307083551 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (310136194240383 / 800000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000)))) (orderedInterval (-9128694548 / 1000000000000) (-9128691874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (279847612308957 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2041039015495893 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000)))) (orderedInterval (-2734937868 / 1000000000000) (-2734930413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1503420100970109 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2576135967987057 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1897570094298963 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000)))) (orderedInterval (57343855 / 1000000000000) (57343874 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks0_1 :
    compactCertificate454.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2911360506704349 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1680874772253621 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2982741779898489 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000)))) (orderedInterval (-2656844754 / 1000000000000) (-2656835310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2786864281868541 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1988837851610253 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2255130151454187 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000)))) (orderedInterval (3477348009 / 1000000000000) (3477348293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1880092411145403 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1661118662729463 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (481456933668837 / 800000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000)))) (orderedInterval (-2830994143 / 1000000000000) (-2830994090 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks0_2 :
    compactCertificate454.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1331735216218239 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1128926691351879 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (706429905701037 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000)))) (orderedInterval (-3339808027 / 1000000000000) (-3339807945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (379920352765779 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1031557662794337 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1408503797968449 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000)))) (orderedInterval (-5325722758 / 1000000000000) (-5325722718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (595570094298963 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2420959368262323 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1617088660904157 / 4000000000000) 0 (IntervalRat.scale (651 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000)))) (orderedInterval (-2679778143 / 1000000000000) (-2679777982 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks0 :
    compactCertificate454.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate454.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate454_chunkChecks0_0
    compactCertificate454_chunkChecks0_1 compactCertificate454_chunkChecks0_2

theorem compactCertificate454_chunkChecks1_0 :
    compactCertificate454.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (651 / 2) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (959047307083551 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (310136194240383 / 800000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000)))) (orderedInterval (17072645057 / 1000000000000) (17072648182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (279847612308957 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2041039015495893 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000)))) (orderedInterval (3226323010 / 1000000000000) (3226334678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1503420100970109 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2576135967987057 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1897570094298963 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000)))) (orderedInterval (445117716 / 1000000000000) (445117748 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks1_1 :
    compactCertificate454.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2911360506704349 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1680874772253621 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2982741779898489 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000)))) (orderedInterval (-4536405265 / 1000000000000) (-4536383658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2786864281868541 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1988837851610253 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2255130151454187 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000)))) (orderedInterval (-1618963392 / 1000000000000) (-1618962925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1880092411145403 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1661118662729463 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (481456933668837 / 800000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000)))) (orderedInterval (1292905879 / 1000000000000) (1292905962 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks1_2 :
    compactCertificate454.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1331735216218239 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1128926691351879 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (706429905701037 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000)))) (orderedInterval (-7548453768 / 1000000000000) (-7548453692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (379920352765779 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1031557662794337 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1408503797968449 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000)))) (orderedInterval (-2195537366 / 1000000000000) (-2195537330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (595570094298963 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2420959368262323 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1617088660904157 / 4000000000000) 1 (IntervalRat.scale (651 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000)))) (orderedInterval (13816755025 / 1000000000000) (13816755188 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks1 :
    compactCertificate454.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate454.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate454_chunkChecks1_0
    compactCertificate454_chunkChecks1_1 compactCertificate454_chunkChecks1_2

theorem compactCertificate454_chunkChecks2_0 :
    compactCertificate454.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (651 / 2) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (959047307083551 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (310136194240383 / 800000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000)))) (orderedInterval (10178670287 / 1000000000000) (10178673962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (279847612308957 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2041039015495893 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000)))) (orderedInterval (5190464529 / 1000000000000) (5190482846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1503420100970109 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2576135967987057 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1897570094298963 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000)))) (orderedInterval (-1360051927 / 1000000000000) (-1360051870 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks2_1 :
    compactCertificate454.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2911360506704349 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1680874772253621 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2982741779898489 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000)))) (orderedInterval (14561116855 / 1000000000000) (14561166381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2786864281868541 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1988837851610253 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2255130151454187 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000)))) (orderedInterval (-8115944152 / 1000000000000) (-8115943375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1880092411145403 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1661118662729463 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (481456933668837 / 800000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000)))) (orderedInterval (5501779234 / 1000000000000) (5501779369 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks2_2 :
    compactCertificate454.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1331735216218239 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1128926691351879 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (706429905701037 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000)))) (orderedInterval (4764657501 / 1000000000000) (4764657574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (379920352765779 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1031557662794337 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1408503797968449 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000)))) (orderedInterval (4066748834 / 1000000000000) (4066748870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (595570094298963 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2420959368262323 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1617088660904157 / 4000000000000) 2 (IntervalRat.scale (651 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000)))) (orderedInterval (5123653880 / 1000000000000) (5123654090 / 1000000000000))) = true
  rfl'

theorem compactCertificate454_chunkChecks2 :
    compactCertificate454.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate454.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate454_chunkChecks2_0
    compactCertificate454_chunkChecks2_1 compactCertificate454_chunkChecks2_2

theorem compactCertificate454_chunkChecks3_0 :
    compactCertificate454.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (651 / 2) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (959047307083551 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (310136194240383 / 800000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000)))) (orderedInterval (-17675255890 / 1000000000000) (-17675251570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (279847612308957 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2041039015495893 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000)))) (orderedInterval (-5364912646 / 1000000000000) (-5364883936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1503420100970109 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2576135967987057 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1897570094298963 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000)))) (orderedInterval (-3351189925 / 1000000000000) (-3351189822 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate454_chunkChecks3_1 :
    compactCertificate454.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2911360506704349 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1680874772253621 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2982741779898489 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000)))) (orderedInterval (34246622823 / 1000000000000) (34246736222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2786864281868541 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1988837851610253 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2255130151454187 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000)))) (orderedInterval (6541649277 / 1000000000000) (6541650574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1880092411145403 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1661118662729463 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (481456933668837 / 800000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000)))) (orderedInterval (-4684986676 / 1000000000000) (-4684986452 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate454_chunkChecks3_2 :
    compactCertificate454.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1331735216218239 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1128926691351879 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (706429905701037 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000)))) (orderedInterval (7305653779 / 1000000000000) (7305653850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (379920352765779 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1031557662794337 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1408503797968449 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000)))) (orderedInterval (2298907298 / 1000000000000) (2298907334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (595570094298963 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2420959368262323 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1617088660904157 / 4000000000000) 3 (IntervalRat.scale (651 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000)))) (orderedInterval (-30199170022 / 1000000000000) (-30199169715 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate454_chunkChecks3 :
    compactCertificate454.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate454.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate454_chunkChecks3_0
    compactCertificate454_chunkChecks3_1 compactCertificate454_chunkChecks3_2

theorem compactCertificate454_chunkChecks4_0 :
    compactCertificate454.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (651 / 2) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18861897265 / 1000000000000) (-18861896579 / 1000000000000), orderedInterval (40029616119 / 1000000000000) (40029616805 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (959047307083551 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50343844487 / 1000000000000) (50343845920 / 1000000000000), orderedInterval (-11091769986 / 1000000000000) (-11091768554 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (310136194240383 / 800000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36154814351 / 1000000000000) (-36154774034 / 1000000000000), orderedInterval (18349568180 / 1000000000000) (18349608497 / 1000000000000)))) (orderedInterval (-11498245135 / 1000000000000) (-11498240032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (279847612308957 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95220363718 / 1000000000000) (95220363781 / 1000000000000), orderedInterval (-6370137707 / 1000000000000) (-6370137643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (751710050484729 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12513301690 / 1000000000000) (12513301692 / 1000000000000), orderedInterval (56808678635 / 1000000000000) (56808678636 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2041039015495893 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30366442434 / 1000000000000) (30366546729 / 1000000000000), orderedInterval (-18071820299 / 1000000000000) (-18071716004 / 1000000000000)))) (orderedInterval (-12954987604 / 1000000000000) (-12954942512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1503420100970109 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14151909523 / 1000000000000) (-14151909368 / 1000000000000), orderedInterval (38664852783 / 1000000000000) (38664852938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2576135967987057 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22393377421 / 1000000000000) (-22393377420 / 1000000000000), orderedInterval (-22051246069 / 1000000000000) (-22051246068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1897570094298963 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26206421039 / 1000000000000) (-26206421038 / 1000000000000), orderedInterval (-25569095030 / 1000000000000) (-25569095029 / 1000000000000)))) (orderedInterval (7748758661 / 1000000000000) (7748758852 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate454_chunkChecks4_1 :
    compactCertificate454.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2911360506704349 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6573606415 / 1000000000000) (-6573606413 / 1000000000000), orderedInterval (28839523665 / 1000000000000) (28839523667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1680874772253621 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (1182217031 / 1000000000000) (1182217032 / 1000000000000), orderedInterval (38903296818 / 1000000000000) (38903296819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2982741779898489 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27522515442 / 1000000000000) (-27522449918 / 1000000000000), orderedInterval (9829152466 / 1000000000000) (9829217989 / 1000000000000)))) (orderedInterval (-78529212804 / 1000000000000) (-78528952762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2786864281868541 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2045492150 / 1000000000000) (2045492151 / 1000000000000), orderedInterval (30157439239 / 1000000000000) (30157439240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1988837851610253 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35733773529 / 1000000000000) (35733774508 / 1000000000000), orderedInterval (-1902005657 / 1000000000000) (-1902004678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2255130151454187 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26713873702 / 1000000000000) (-26713843751 / 1000000000000), orderedInterval (20409050032 / 1000000000000) (20409079983 / 1000000000000)))) (orderedInterval (18798553439 / 1000000000000) (18798555621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1880092411145403 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15364171002 / 1000000000000) (-15364170764 / 1000000000000), orderedInterval (33458627464 / 1000000000000) (33458627702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1661118662729463 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38401741443 / 1000000000000) (38401741461 / 1000000000000), orderedInterval (7588926322 / 1000000000000) (7588926341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (481456933668837 / 800000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-17808568416 / 1000000000000) (-17808567739 / 1000000000000), orderedInterval (27230180896 / 1000000000000) (27230181572 / 1000000000000)))) (orderedInterval (-11893499391 / 1000000000000) (-11893499009 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate454_chunkChecks4_2 :
    compactCertificate454.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1331735216218239 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28503651587 / 1000000000000) (28503651588 / 1000000000000), orderedInterval (33118818246 / 1000000000000) (33118818247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1128926691351879 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12818579344 / 1000000000000) (12818579345 / 1000000000000), orderedInterval (45708580523 / 1000000000000) (45708580524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (706429905701037 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59690533640 / 1000000000000) (59690533651 / 1000000000000), orderedInterval (6291810148 / 1000000000000) (6291810159 / 1000000000000)))) (orderedInterval (-5274862993 / 1000000000000) (-5274862924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (379920352765779 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81748106702 / 1000000000000) (81748106716 / 1000000000000), orderedInterval (4021675863 / 1000000000000) (4021675877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1031557662794337 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43433078472 / 1000000000000) (43433078473 / 1000000000000), orderedInterval (24043406995 / 1000000000000) (24043406996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1408503797968449 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36937837494 / 1000000000000) (36937837495 / 1000000000000), orderedInterval (21007636620 / 1000000000000) (21007636621 / 1000000000000)))) (orderedInterval (-4290407943 / 1000000000000) (-4290407904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (595570094298963 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58838262840 / 1000000000000) (-58838251820 / 1000000000000), orderedInterval (28723786949 / 1000000000000) (28723797969 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2420959368262323 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9657103389 / 1000000000000) (9657103403 / 1000000000000), orderedInterval (-30969046191 / 1000000000000) (-30969046178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1617088660904157 / 4000000000000) 4 (IntervalRat.scale (651 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8202338949 / 1000000000000) (8202338964 / 1000000000000), orderedInterval (-38836081699 / 1000000000000) (-38836081684 / 1000000000000)))) (orderedInterval (-12888916109 / 1000000000000) (-12888915623 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate454_chunkChecks4 :
    compactCertificate454.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate454.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate454_chunkChecks4_0
    compactCertificate454_chunkChecks4_1 compactCertificate454_chunkChecks4_2

theorem compactCertificate454_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate454.chunkCheck r b = true :=
  compactCertificate454.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate454_chunkChecks0
    · exact compactCertificate454_chunkChecks1
    · exact compactCertificate454_chunkChecks2
    · exact compactCertificate454_chunkChecks3
    · exact compactCertificate454_chunkChecks4)

theorem compactCertificate454_coefficient0 :
    compactCertificate454.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate454_coefficient1 :
    compactCertificate454.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate454_coefficient2 :
    compactCertificate454.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate454_coefficient3 :
    compactCertificate454.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate454_coefficient4 :
    compactCertificate454.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate454_coefficients : ∀ r : Fin 5,
    compactCertificate454.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate454_coefficient0
  · exact compactCertificate454_coefficient1
  · exact compactCertificate454_coefficient2
  · exact compactCertificate454_coefficient3
  · exact compactCertificate454_coefficient4

theorem compactCertificate454_lower : (1 : ℚ) ≤ compactCertificate454.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate454, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate454_proves {t : ℝ} (ht : t ∈ compactCertificate454.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate454.proves compactCertificate454_states compactCertificate454_chunks
    compactCertificate454_coefficients compactCertificate454_lower ht

end Erdos232
